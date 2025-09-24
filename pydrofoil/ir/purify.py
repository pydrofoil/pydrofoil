"""
Purify 'almost pure' functions.

'Almost pure' means that a function is pure except for reading some global
state.
The result is a function that splits the reading of the state and the pure part
into 2 functions.
"""

from pydrofoil import makecode, ir

from collections import defaultdict


def purify(codegen, graph):
    # type: (makecode.Codegen, ir.Graph) -> None
    global_reads = defaultdict(list)  # type: dict[str, list[ir.Operation]]
    for block in graph.iterblocks():
        for i, op in enumerate(block.operations):
            if not isinstance(op, ir.GlobalRead):
                continue
            global_reads[op.name].append(op)
            block.operations[i] = None  # type: ignore
        block.operations = [op for op in block.operations if op is not None]

    # Build the new body of 'graph'.
    # Reads all global state once and calls the pure part as a new function.
    block = ir.Block()
    new_graph_name = graph.name.lstrip("z") + "_pure_core"
    # List of parameters that the new function is called with.
    new_params = list(graph.args)  # type: list[ir.Value]
    # List of arguments of the new function
    new_args = list(graph.args)  # type: list[ir.Argument]
    replacements = {}
    for ops in global_reads.values():
        op = ops[0]
        block.operations.append(op)
        new_params.append(op)
        arg = ir.Argument(op.name, op.resolved_type)
        new_args.append(arg)
        for op in ops:
            replacements[op] = arg
    call_to_new_function = block.emit(
        ir.Operation, new_graph_name, new_params, graph.find_return_type()
    )
    block.next = ir.Return(call_to_new_function)
    # We move the blocks from the original function to our new, pure function.
    new_graph = ir.Graph(new_graph_name, new_args, graph.startblock)
    new_graph.replace_ops(replacements)
    graph.startblock = block
    codegen.add_graph(new_graph)
    graph.check()
    new_graph.check()
