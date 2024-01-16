from pydrofoil import parse, makecode, types, supportcode
from collections import defaultdict



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


