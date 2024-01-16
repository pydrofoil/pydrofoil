import time

from pydrofoil import ir, types

def bfs_edges(start):
    from collections import deque
    todo = deque([start])
    seen = set()
    while todo:
        block = todo.popleft()
        if block in seen:
            continue
        seen.add(block)
        successors = block.next_blocks()
        todo.extend(successors)
        for succ in successors:
            yield block, succ


def split_graph(graph, codegen, functyp, next_name, min_size, start_block=None):
    if start_block is None:
        start_block = graph.startblock
    preds = graph.make_entrymap()
    all_blocks = set(graph.iterblocks())
    def is_end_block(block):
        return len(block.next.next_blocks()) == 0
    # split graph, starting from exit edges (ie an edge going to a block
    # ending with Return or Raise)
    graph1blocks = set()
    transfer_blocks = set()

    def view():
        colors = {block: "green" if block in graph1blocks else "blue" for block in all_blocks}
        for block in all_blocks:
            if block in transfer_blocks:
                colors[block] = 'red'
            elif block in graph1blocks:
                colors[block] = 'green'
            elif is_end_block(block):
                colors[block] = 'grey'
        view_blocks(graph, colors)

    for source, target in bfs_edges(start_block):
        if not is_end_block(target):
            continue
        # approach: from the edge going to the exit block, extend by adding
        # predecessors up to fixpoint
        graph1blocks.add(target)
        todo = [source]
        while todo:
            block = todo.pop()
            if block in graph1blocks:
                continue
            graph1blocks.add(block)
            todo.extend(preds[block])
        # add all end blocks that are reachable from the blocks in graph1blocks.
        # also compute blocks where we need to transfer from graph1blocks to graph2
        transfer_blocks = set()
        for block in list(graph1blocks):
            for succ in block.next.next_blocks():
                if succ in graph1blocks:
                    continue
                if is_end_block(succ):
                    graph1blocks.add(succ)
                else:
                    transfer_blocks.add(succ)
        # if we only have a single transfer_block left, we have a potential
        # split
        if len(transfer_blocks) == 1:
            if len(graph1blocks) > min_size:
                break
        if len(graph1blocks) == len(all_blocks):
            # didn't manage to split
            raise CantSplitError
    else:
        raise CantSplitError
    # compute graph2blocks
    graph2blocks = set()
    for block in graph.iterblocks():
        if block not in graph1blocks:
            graph2blocks.add(block)
    if len(graph2blocks) < min_size // 3:
        raise CantSplitError
    # add reachable end blocks
    for block in list(graph2blocks):
        for block in block.next.next_blocks():
            if is_end_block(block):
                graph2blocks.add(block)
    # consistency check:
    for block in graph.iterblocks():
        assert block in graph1blocks or block in graph2blocks
        if block in graph1blocks and block in graph2blocks:
            import pdb;pdb.set_trace() # this might be sharing blocks
            assert is_end_block(block)
    transferblock, = transfer_blocks
    assert transferblock not in graph1blocks
    assert transferblock in graph2blocks
    # compute needed arguments
    graph1_produces = set(graph.args)
    for block in graph1blocks:
        graph1_produces.update(block.operations)

    graph2_needs = set()
    def add_used(args):
        for used in args:
            if used in graph1_produces:
                graph2_needs.add(used)
    for block in graph2blocks:
        for op in block.operations:
            add_used(op.getargs())
        add_used(block.next.getargs())
    args_graph2_needs = list(graph2_needs)

    # insert call to next function in graph
    calling_blocks = preds[transferblock]
    newblock = ir.Block()
    op = ir.Operation(next_name, args_graph2_needs, functyp.restype)
    newblock.operations.append(op)
    newblock.next = ir.Return(op)
    for block in calling_blocks:
        block.next.replace_next(transferblock, newblock)

    replacements = {}
    newargs = []
    argtyps = []
    for index, arg in enumerate(args_graph2_needs):
        newargs.append(ir.Argument('a%i' % index, arg.resolved_type))
        replacements[arg] = newargs[-1]
        argtyps.append(arg.resolved_type)
    graph2typ = types.Function(types.Tuple(tuple(argtyps)), functyp.restype)
    graph2 = ir.Graph(next_name, newargs, transferblock)
    graph2.replace_ops(replacements)
    graph.check()
    codegen.print_debug_msg("previous size", len(all_blocks), "afterwards:", len(graph1blocks), len(graph2blocks))
    return graph2, graph2typ, len(graph2blocks)


class CantSplitError(Exception):
    pass


def split_completely(graph, funcnode, functyp, codegen, min_size=100):
    t1 = time.time()
    changed = ir.duplicate_end_blocks(graph, codegen)
    if changed:
        ir.light_simplify(graph, codegen)
    next_name_base = graph.name + "_next_"
    i = 0
    while 1:
        next_name = next_name_base + str(i)
        try:
            graph2, graph2typ, remaining_blocks = split_graph(graph, codegen, functyp, next_name, min_size)
        except CantSplitError:
            codegen.print_debug_msg("couldn't split!", len(list(graph.iterblocks())))
            break
        yield graph2, graph2typ
        if remaining_blocks < min_size:
            break
        graph = graph2
        i += 1
    t2 = time.time()
    codegen.print_debug_msg("Splitting", next_name_base, "took", t2 - t1)


def view_blocks(graph, colors=None):
    from rpython.translator.tool.make_dot import DotGen
    from dotviewer import graphclient
    import pytest
    import os
    if colors is None:
        colors = {graph.startblock: "green"}
    dotgen = DotGen('G')
    num_blocks = 0
    for block in graph.iterblocks():
        dotgen.emit_node(str(id(block)), label=' ', shape="box", fillcolor=colors.get(block, 'grey'))
        for nextblock in block.next.next_blocks():
            dotgen.emit_edge(str(id(block)), str(id(nextblock)))
        num_blocks += 1
    p = pytest.ensuretemp("pyparser").join("temp.dot")
    p.write(dotgen.generate(target=None))
    if num_blocks > 200:
        p2 = p.new(ext=".plain")
        os.system("twopi -Tplain %s > %s" % (p, p2))
        p = p2
    graphclient.display_dot_file(str(p))
