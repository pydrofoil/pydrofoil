from pydrofoil import parse, makecode, types, supportcode
from collections import defaultdict


# optimize operation ASTs before generating code


def optimize_blocks(blocks, codegen, predefined=None, register_names=None):
    inline(blocks, codegen.inlinable_functions)
    move_regs_into_locals(blocks, register_names)
    do_replacements(identify_replacements(blocks, predefined))
    specialize_ops(blocks, codegen)
    optimize_gotos(blocks)


def find_decl_defs_uses(blocks, predefined=None):
    defs = defaultdict(list)
    uses = defaultdict(list)
    decls = {}
    if predefined:
        for var, typ in predefined.iteritems():
            decls[var] = (blocks[0], None)
            if var != "return_":
                defs[var].append((blocks[0], None))
    for _, block in sorted(blocks.items()):
        for i, op in enumerate(block):
            used_vars = op.find_used_vars()
            for var in used_vars:
                uses[var].append((block, i))
            if isinstance(op, (parse.Assignment, parse.Operation)):
                defs[op.result].append((block, i))
            elif isinstance(op, parse.LocalVarDeclaration):
                assert op.name not in decls
                decls[op.name] = (block, i)
    return decls, defs, uses


def inline(blocks, inlinable_functions):
    for num, block in blocks.iteritems():
        index = 0
        while index < len(block):
            op = block[index]
            if isinstance(op, parse.Operation) and op.name in inlinable_functions:
                functionast, targetblocks = inlinable_functions[op.name]
                newops = copy_ops(op, functionast, targetblocks)
                if newops is not None:
                    block[index : index + 1] = newops
                    index = 0
                    continue
            index += 1


def copy_ops(op, functionast, targetblocks):
    assert len(targetblocks) == 1
    block = targetblocks[0]
    if len(block) != 2:
        return None
    targetop, endop = block
    if not isinstance(endop, parse.End):
        return
    if not isinstance(targetop, parse.Assignment) or targetop.result != "return":
        return None
    expr = targetop.value
    for argname, argexpr in zip(functionast.args, op.args):
        expr = expr.replace_var(argname, argexpr)
    return [parse.Assignment(op.result, expr, op.sourcepos, op.resolved_type)]


def specialize_ops(blocks, codegen):
    v = OptVisitor(codegen)
    for num, block in blocks.iteritems():
        for i, op in enumerate(block):
            while 1:
                v.changed = False
                res = op.mutate_with(v)
                if res is not None:
                    block[i] = op = res
                elif not v.changed:
                    break



class CollectSourceVisitor(parse.Visitor):
    def __init__(self):
        self.seen = set()

    def default_visit(self, ast):
        sourcepos = getattr(ast, "sourcepos", None)
        sourcepos = self._parse(sourcepos)
        if sourcepos:
            self.seen.add(sourcepos)
        for key, value in ast.__dict__.items():
            if isinstance(value, parse.BaseAst):
                self.visit(value)
            elif (
                isinstance(value, list)
                and value
                and isinstance(value[0], parse.BaseAst)
            ):
                for i, item in enumerate(value):
                    self.visit(item)

    def _parse(self, sourcepos):
        if sourcepos is None:
            return None
        sourcepos = sourcepos.lstrip("`")
        l = sourcepos.split(" ", 1)
        if len(l) == 1:
            return None
        filenum, rest = l
        from_, to = rest.split("-", 1)
        fromline, frompos = from_.split(":", 1)
        toline, topos = to.split(":", 1)
        return int(filenum), int(fromline), int(frompos), int(toline), int(topos)


class OptVisitor(parse.Visitor):
    def __init__(self, codegen):
        self.codegen = codegen

    def visit_CastExpr(self, cast):
        if isinstance(cast.expr, parse.CastExpr):
            return parse.CastExpr(cast.expr.expr, cast.resolved_type)
        if (
            isinstance(cast.expr, parse.OperationExpr)
            and cast.expr.resolved_type is cast.resolved_type
        ):
            return cast.expr

    def visit_OperationExpr(self, expr):
        assert expr.resolved_type is not None
        name = self._builtinname(expr.name)
        if name in supportcode.all_unwraps:
            specs, unwrapped_name = supportcode.all_unwraps[name]
            # these are unconditional unwraps, just rewrite them right here
            assert len(specs) == len(expr.args)
            newargs = []
            for argspec, arg in zip(specs, expr.args):
                if argspec == "o":
                    newargs.append(arg)
                elif argspec == "i":
                    newargs.append(self._convert_to_machineint(arg))
                else:
                    assert 0, "unknown spec"
            return parse.OperationExpr(
                "@" + unwrapped_name,
                newargs,
                expr.resolved_type,
                expr.sourcepos,
            )
        meth = getattr(self, "optimize_%s" % name.lstrip("@"), None)
        if not meth:
            return None
        try:
            res = meth(expr)
        except NoMatchException:
            return None
        if res is None:
            return
        restypold = getattr(expr, 'resolved_type', None)
        restypnew = getattr(res, 'resolved_type', None)
        assert restypold is restypnew or restypold is types.MachineInt() and isinstance(res, parse.Number)
        return res

    def visit_Operation(self, operation):
        assert operation.resolved_type is not None
        if operation.name == "$zinternal_vector_update":
            return
        expr = parse.OperationExpr(
            operation.name,
            operation.args,
            operation.resolved_type,
            operation.sourcepos,
        )
        return parse.Assignment(
            operation.result,
            expr,
            operation.sourcepos,
            operation.resolved_type,
        )

    def visit_Assignment(self, expr):
        while isinstance(expr.value, parse.CastExpr):
            expr.value = expr.value.expr

    def visit_FieldAccess(self, expr):
        if not isinstance(expr.obj, parse.StructConstruction):
            return
        index = expr.obj.fieldnames.index(expr.element)
        return expr.obj.fieldvalues[index]

    def visit_StructElementAssignment(self, assign):
       if assign.resolved_type != assign.value.resolved_type:
           value = parse.CastExpr(assign.value, assign.resolved_type)
           return parse.StructElementAssignment(assign.obj, assign.fields, value, assign.resolved_type, assign.sourcepos)

    def visit_GeneralAssignment(self, assign):
        lhs = assign.lhs
        rhs = assign.rhs
        if isinstance(rhs, parse.Operation):
            value = parse.OperationExpr(rhs.name, rhs.args, rhs.resolved_type)
        else:
            return None
        if isinstance(lhs, parse.StructElementAssignment):
            return parse.StructElementAssignment(
                lhs.obj, lhs.fields, value, lhs.resolved_type, assign.sourcepos
            )
        assert isinstance(lhs, parse.RefAssignment)
        return parse.RefAssignment(lhs.ref, value, lhs.resolved_type, assign.sourcepos)

    def _gettyp(self, expr):
        assert expr.resolved_type is not None
        return expr.resolved_type


# optimize_gotos


def collect_jump_to_jump(blocks):
    res = {}
    for num, block in blocks.iteritems():
        if num == 0 or len(block) > 1:
            continue
        (op,) = block
        if not isinstance(op, parse.Goto):
            continue
        res[num] = op.target
    for source, target in res.iteritems():
        while target in res:
            target = res[source] = res[target]
    return res


def optimize_gotos(blocks):
    jumps = collect_jump_to_jump(blocks)
    if not jumps:
        return
    for num, block in blocks.iteritems():
        for op in block:
            if not hasattr(op, "target"):
                continue
            if op.target in jumps:
                op.target = jumps[op.target]
    for useless in jumps:
        del blocks[useless]


def _get_successors(block):
    result = set()
    for op in block:
        if not hasattr(op, "target"):
            continue
        result.add(op.target)
    return result


def compute_predecessors(G):
    result = defaultdict(list)
    for num, succs in G.iteritems():
        for succ in succs:
            result[succ].append(num)
        result[num].append(num)
    return result


def _compute_dominators(G, start=0):
    preds = compute_predecessors(G)
    # initialize
    dominators = {}
    for node in G:
        dominators[node] = set(G)
    dominators[start] = {start}

    # fixpoint
    changed = True
    while changed:
        changed = False
        for node in G:
            if node == start:
                continue
            dom = set(G).intersection(*[dominators[x] for x in preds[node]])
            dom.add(node)
            if dom != dominators[node]:
                changed = True
                dominators[node] = dom
    return dominators


def immediate_dominators(G, start=0):
    if start not in G:
        return {}
    res = {}
    dominators = _compute_dominators(G, start)
    for node in G:
        if node == start:
            continue
        doms = dominators[node]
        for candidate in doms:
            if candidate == node:
                continue
            for otherdom in doms:
                if otherdom == node or otherdom == candidate:
                    continue
                if candidate in dominators[otherdom]:
                    break
            else:
                break
        res[node] = candidate
    return res

def _extract_graph(blocks):
    return {num: _get_successors(block) for (num, block) in blocks.iteritems()}

def immediate_dominators_blocks(blocks):
    G = _extract_graph(blocks)
    return immediate_dominators(G)

def bfs_graph(G, start=0):
    from collections import deque
    todo = deque([start])
    seen = set()
    res = []
    while todo:
        node = todo.popleft()
        if node in seen:
            continue
        seen.add(node)
        todo.extend(G[node])
        res.append(node)
    return res

def bfs_edges(G, start=0):
    from collections import deque
    todo = deque([start])
    seen = set()
    res = []
    while todo:
        node = todo.popleft()
        if node in seen:
            continue
        seen.add(node)
        successors = G[node]
        todo.extend(successors)
        for succ in successors:
            res.append((node, succ))
    return res

def view_blocks(blocks):
    from rpython.translator.tool.make_dot import DotGen
    from dotviewer import graphclient
    import pytest
    dotgen = DotGen('G')
    G = {num: _get_successors(block) for (num, block) in blocks.iteritems()}
    idom = immediate_dominators(G)
    for num, block in blocks.iteritems():
        label = [str(num)] + [str(op)[:100] for op in block]
        dotgen.emit_node(str(num), label="\n".join(label), shape="box")

    for start, succs in G.iteritems():
        for finish in succs:
            color = "green"
            dotgen.emit_edge(str(start), str(finish), color=color)
    for finish, start in idom.iteritems():
        color = "red"
        dotgen.emit_edge(str(start), str(finish), color=color)

    p = pytest.ensuretemp("pyparser").join("temp.dot")
    p.write(dotgen.generate(target=None))
    graphclient.display_dot_file(str(p))


# graph splitting

class CantSplitError(Exception):
    pass

def split_graph(blocks, min_size=6, start_node=0):
    G = _extract_graph(blocks)
    preds = compute_predecessors(G)
    # split graph, starting from exit edges (ie an edge going to a block
    # ending with End)
    graph1 = {}
    for source, target in bfs_edges(G, start_node):
        if not isinstance(blocks[target][-1], parse.End):
            continue
        # approach: from the edge going to the 'End' node, extend by adding
        # predecessors up to fixpoint
        graph1[target] = blocks[target]
        todo = [source]
        while todo:
            node = todo.pop()
            if node in graph1:
                continue
            graph1[node] = blocks[node]
            todo.extend(preds[node])
        # add all end nodes that are reachable from the nodes in graph1.
        # also compute nodes where we need to transfer from graph1 to graph2
        transfer_nodes = set()
        for node in list(graph1):
            for succ in G[node]:
                if succ in graph1:
                    continue
                block = blocks[succ]
                if isinstance(block[-1], parse.FunctionEndingStatement):
                    graph1[succ] = block
                else:
                    transfer_nodes.add(succ)
        # try to remove some transfer nodes, if they are themselves only a
        # single block away from an end block (happens with exceptions)
        for node in list(transfer_nodes):
            successors = G[node]
            if len(successors) > 1:
                continue
            succ, = successors
            block = blocks[succ]
            if not isinstance(block[-1], parse.FunctionEndingStatement):
                continue
            graph1[node] = blocks[node]
            graph1[succ] = block
            transfer_nodes.remove(node)

        # if we only have a single transfer_node left, we have a potential
        # split
        if len(transfer_nodes) == 1:
            if len(graph1) > min_size:
                break
        if len(graph1) == len(blocks):
            # didn't manage to split
            raise CantSplitError
    else:
        raise CantSplitError
    # compute graph2
    graph2 = {}
    for node in G:
        if node not in graph1:
            graph2[node] = blocks[node]
    # add reachable end nodes
    for node in list(graph2):
        for succ in G[node]:
            block = blocks[succ]
            if isinstance(block[-1], parse.FunctionEndingStatement):
                graph2[succ] = block
    # consistency check:
    for num, block in blocks.iteritems():
        assert num in graph1 or num in graph2
        if num in graph1 and num in graph2:
            assert isinstance(blocks[num][-1], parse.FunctionEndingStatement)
    transferpc, = transfer_nodes
    assert transferpc not in graph1
    assert transferpc in graph2
    return graph1, graph2, transferpc
