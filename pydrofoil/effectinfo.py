from collections import defaultdict
from pydrofoil.ir import (
    FieldWrite,
    GlobalRead,
    Graph,
    GlobalWrite,
    Operation,
    FieldAccess,
)
from pydrofoil.types import Struct


class EffectInfo(object):
    def __init__(
        self,
        register_reads=frozenset(),
        register_writes=frozenset(),
        struct_reads=frozenset(),
        struct_writes=frozenset(),
        called_builtins=frozenset(),
    ):
        # type: (frozenset[str], frozenset[str], frozenset[tuple[Struct, str]], frozenset[tuple[Struct, str]], frozenset[str]) -> None
        self.register_reads = register_reads
        self.register_writes = register_writes
        self.struct_reads = struct_reads
        self.struct_writes = struct_writes
        self.called_builtins = called_builtins

    def add_register_write(self, register_name):
        # type: (str) -> EffectInfo
        return self.extend(
            EffectInfo(register_writes=frozenset({register_name}))
        )

    def add_register_read(self, register_name):
        # type: (str) -> EffectInfo
        return self.extend(
            EffectInfo(register_reads=frozenset({register_name}))
        )

    def add_struct_write(self, struct_type, field_name):
        # type: (Struct, str) -> EffectInfo
        return self.extend(
            EffectInfo(struct_writes=frozenset({(struct_type, field_name)}))
        )

    def add_struct_read(self, struct_type, field_name):
        # type: (Struct, str) -> EffectInfo
        return self.extend(
            EffectInfo(struct_reads=frozenset({(struct_type, field_name)}))
        )

    def add_called_builtin(self, builtin_name):
        # type: (str) -> EffectInfo
        return self.extend(
            EffectInfo(called_builtins=frozenset({builtin_name}))
        )

    def extend(self, other):
        # type: (EffectInfo) -> EffectInfo
        """Create a new EffectInfo with all effects from 'other' added."""
        return EffectInfo(
            self.register_reads | other.register_reads,
            self.register_writes | other.register_writes,
            self.struct_reads | other.struct_reads,
            self.struct_writes | other.struct_writes,
            self.called_builtins | other.called_builtins,
        )

    def __repr__(self):
        return (
            "EffectInfo("
            "register_reads=%s, "
            "register_writes=%s, "
            "struct_reads=%s, "
            "struct_writes=%s, "
            "called_builtins=%s)"
        ) % (
            self.register_reads,
            self.register_writes,
            self.struct_reads,
            self.struct_writes,
            self.called_builtins,
        )

    def __eq__(self, other):
        return (
            isinstance(other, EffectInfo)
            and self.register_reads == other.register_reads
            and self.register_writes == other.register_writes
            and self.struct_reads == other.struct_reads
            and self.struct_writes == other.struct_writes
            and self.called_builtins == other.called_builtins
        )

    def __ne__(self, other):
        return not self == other


BOTTOM = EffectInfo()


class _EffectComputationState(object):
    def __init__(self, graph_map, methods):
        # type: (dict[str, Graph], dict[str, dict[str, Graph]]) -> None
        self.effect_map = defaultdict(
            EffectInfo
        )  # type: dict[str, EffectInfo]
        self.caller_map = defaultdict(set)  # type: dict[str, set[str]]
        self.todo_set = set()  # type: set[str]
        self.graph_map = graph_map
        self.methods = methods

    def analyze_all(self):
        self.todo_set.update(self.graph_map)
        for method_dict in self.methods.itervalues():
            for graph in method_dict.itervalues():
                self.todo_set.add(graph.name)
        while self.todo_set:
            graph_name = self.todo_set.pop()
            graph = self.graph_map[graph_name]
            effect_info = self._get_effect_info_and_update_caller_map(graph)
            old_effects = self.effect_map[graph_name]
            self.effect_map[graph_name] = effect_info

            # Update all callers
            if old_effects != effect_info:
                self.todo_set.update(self.caller_map[graph_name])

        return self.effect_map

    def _get_effect_info_and_update_caller_map(self, graph):
        # type: (Graph) -> EffectInfo
        effect_info = local_effects(graph)
        # Add effects from all called functions
        for block in graph.iterblocks():
            for op in block.operations:
                if type(op) is not Operation:
                    continue
                if op.name in self.methods:
                    callees = [
                        called_graph.name
                        for called_graph in self.methods[op.name].itervalues()
                    ]
                elif op.name in self.graph_map:
                    callees = [op.name]
                else:
                    continue
                for callee_name in callees:
                    effect_info = effect_info.extend(
                        self.effect_map[callee_name]
                    )
                    self.caller_map[callee_name].add(graph.name)

        return effect_info


def local_effects(graph):
    # type: (Graph) -> EffectInfo
    result = EffectInfo()
    for block in graph.iterblocks():
        for op in block.operations:
            if isinstance(op, GlobalWrite):
                result = result.add_register_write(op.name)
            elif isinstance(op, GlobalRead):
                result = result.add_register_read(op.name)
            elif isinstance(op, FieldWrite):
                result = result.add_struct_write(
                    op.args[0].resolved_type, op.name
                )
            elif isinstance(op, FieldAccess):
                result = result.add_struct_read(
                    op.args[0].resolved_type, op.name
                )
            elif isinstance(op, Operation) and op.name[0] in ("@", "$"):
                result = result.add_called_builtin(op.name)

    return result


def compute_all_effects(graph_map, methods={}):
    # type: (dict[str, Graph], dict[str, dict[str, Graph]]) -> dict[str, EffectInfo]
    state = _EffectComputationState(graph_map, methods)
    return state.analyze_all()
