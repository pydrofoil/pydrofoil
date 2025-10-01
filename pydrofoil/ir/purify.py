"""
Purify 'almost pure' functions.

'Almost pure' means that a function is pure except for reading some global
state.
The result is a function that splits the reading of the state and the pure part
into 2 functions.
"""
from __future__ import print_function
from pydrofoil import makecode, ir

from collections import defaultdict

from pydrofoil.effectinfo import compute_all_effects_and_call_graph, EffectInfo


def purify(codegen, graph):
    # type: (makecode.Codegen, ir.Graph) -> ir.Graph
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
    codegen.all_graph_by_name[new_graph_name] = new_graph
    graph.check()
    new_graph.check()
    return new_graph


def purify_all_graphs(codegen):
    # type: (makecode.Codegen) -> None
    codegen.print_highlevel_task("PURIFY")
    effects, caller_map = compute_all_effects_and_call_graph(codegen)
    work_list = set(codegen.all_graph_by_name.values())
    purified = set()  # type: set[ir.Graph]
    modified = set()  # type: set[ir.Graph]

    while work_list:
        graph = work_list.pop()
        if graph not in purified and _can_purify(
            codegen, effects[graph.name], graph
        ):
            purify(codegen, graph)
            print("PURIFIED", graph.name)
            codegen.inlinable_functions[graph.name] = graph
            purified.add(graph)
            modified.add(graph)
            for caller_name in caller_map[graph.name]:
                caller_graph = codegen.all_graph_by_name[caller_name]
                ir.inline(caller_graph, codegen)
                modified.add(caller_graph)
                work_list.add(caller_graph)
    for graph in modified:
        ir.light_simplify(graph, codegen)


def _can_purify(codegen, effect_info, graph):
    # type: (makecode.Codegen, EffectInfo, ir.Graph) -> bool
    if (
        effect_info.struct_reads
        or effect_info.struct_writes
        or effect_info.register_writes
    ):
        return False

    for builtin_name in effect_info.called_builtins:
        if not ir.builtin_is_pure(builtin_name, codegen):
            return False

    # Check for any global reads
    for block in graph.iterblocks():
        for op in block.operations:
            if isinstance(op, ir.GlobalRead):
                return True
    # Function is already pure, so no purification can be done.
    return False
