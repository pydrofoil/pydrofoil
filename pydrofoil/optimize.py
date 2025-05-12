from pydrofoil import ir, types

@ir.repeat
def merge_phi_blocks(graph, codegen):
    if graph.has_loop:
        return False
    changed = False
    for block in graph.iterblocks():
        if len(block.operations) != 1:
            continue
        phi1, = block.operations
        if not isinstance(phi1, ir.Phi):
            continue
        next = block.next
        if not isinstance(next, ir.Goto):
            continue
        nextblock = next.target
        phis = [op for op in nextblock.operations if isinstance(op, ir.Phi)]
        if len(phis) != 1:
            continue
        phi2, = phis
        pos = phi2.prevvalues.index(phi1)
        phi2.prevvalues[pos: pos + 1] = phi1.prevvalues
        phi2.prevblocks[pos: pos + 1] = phi1.prevblocks
        for prevblock in phi1.prevblocks:
            prevblock.next.replace_next(block, nextblock)
            changed = True
    return changed

@ir.repeat
def fix_union_check_switch(graph, codegen):
    def used_in(blocks, op):
        for block in blocks:
            for op in block.operations:
                if op is None:
                    continue
                for arg in op.getargs():
                    if arg is op:
                        return True
            for arg in block.next.getargs():
                if arg is op:
                    return True
        return False
    changed = False

    for block in graph.iterblocks():
        if len(block.operations) != 2:
            continue
        phi, unioncheck = block.operations
        if not isinstance(phi, ir.Phi):
            continue
        if not isinstance(unioncheck, ir.UnionVariantCheck):
            continue
        if not isinstance(block.next, ir.ConditionalGoto) or block.next.booleanvalue is not unioncheck:
            continue
        if not all(prev.is_union_creation() for prev in phi.prevvalues):
            continue
        trueblocks = set(graph.iterblocks(block.next.truetarget))
        falseblocks = set(graph.iterblocks(block.next.falsetarget))
        joinblocks = trueblocks.intersection(falseblocks)
        if used_in(joinblocks, phi):
            continue
        truevalues = []
        trueprevblocks = []
        falsevalues = []
        falseprevblocks = []
        trueblock = ir.Block()
        for prev, prevblock in zip(phi.prevvalues, phi.prevblocks):
            assert isinstance(prevblock.next, ir.Goto)
            assert prevblock.next.target is block
            if prev.name == unioncheck.name:
                falsevalues.append(prev)
                falseprevblocks.append(prevblock)
            else:
                truevalues.append(prev)
                trueprevblocks.append(prevblock)
                prevblock.next.target = trueblock
        truephi = trueblock.emit_phi(trueprevblocks, truevalues, phi.resolved_type)
        # the phi becomes valid only in the false case
        phi.prevvalues = falsevalues
        phi.prevblocks = falseprevblocks
        trueblock.next = ir.Goto(block.next.truetarget)
        block.next = ir.Goto(block.next.falsetarget)
        replacements = {phi: truephi}
        for trueblock in trueblocks:
            for op in trueblock.operations:
                op.replace_ops(replacements)
            block.next.replace_ops(replacements)
        graph.check()
        ir._remove_unreachable_phi_prevvalues(graph)
        return True # inefficient
    return False
