from collections import defaultdict
from pydrofoil.ir import GlobalRead, Graph, GlobalWrite, Operation

class EffectInfo(object):

    def __init__(self, register_reads=frozenset(), register_writes=frozenset()):
        self.register_reads = register_reads  # type: frozenset[str]
        self.register_writes = register_writes  # type: frozenset[str]

    def add_write(self, register_name):
        # type: (str) -> EffectInfo
        return EffectInfo(
            self.register_reads,
            self.register_writes | {register_name},
        )

    def add_read(self, register_name):
        # type: (str) -> EffectInfo
        return EffectInfo(
            self.register_reads | {register_name},
            self.register_writes,
        )

    def extend(self, other):
        # type: (EffectInfo) -> EffectInfo
        """Create a new EffectInfo with all effects from 'other' added."""
        return EffectInfo(
            self.register_reads | other.register_reads,
            self.register_writes | other.register_writes,
        )

    def __repr__(self):
        return (
            "EffectInfo(register_reads=%s, register_writes=%s)"
            % (self.register_reads, self.register_writes)
        )

    def __eq__(self, other):
        return (
            isinstance(other, EffectInfo)
            and self.register_reads == other.register_reads
            and self.register_writes == other.register_writes
        )

    def __ne__(self, other):
        return not self == other


class _EffectComputationState(object):
    def __init__(self):
        self.effect_map = defaultdict(EffectInfo)  # type: dict[str, EffectInfo]
        self.caller_map = defaultdict(set) # type: dict[str, set[str]]
        self.todo_set = set()  # type: set[str]

    def analyze_all(self, graph_map):
        # type: (dict[str, Graph]) -> dict[str, EffectInfo]
        self.todo_set.update(graph_map)
        while self.todo_set:
            graph_name = self.todo_set.pop()
            graph = graph_map[graph_name]
            effect_info = self._get_effect_info(graph)
            # update caller map
            for block in graph.iterblocks():
                for op in block.operations:
                    if isinstance(op, Operation) and op.name in graph_map:
                        if op.name == graph_name:
                            continue
                        self.caller_map[op.name].add(graph_name)

            old_effects = self.effect_map[graph_name]
            self.effect_map[graph_name] = effect_info

            # Update all callers
            if old_effects != effect_info:
                self.todo_set.update(self.caller_map[graph_name])

        return self.effect_map

    def _get_effect_info(self, graph):
        # type: (Graph) -> EffectInfo
        effect_info = local_effects(graph)
        # Add effects from all called functions
        for block in graph.iterblocks():
            for op in block.operations:
                if isinstance(op, Operation) and op.name in self.effect_map:
                    effect_info = effect_info.extend(self.effect_map[op.name])
        return effect_info


def local_effects(graph):
    # type: (Graph) -> EffectInfo
    result = EffectInfo()
    for block in graph.iterblocks():
        for op in block.operations:
            if isinstance(op, GlobalWrite):
                result = result.add_write(op.name)
            elif isinstance(op, GlobalRead):
                result = result.add_read(op.name)
    return result


def compute_all_effects(graph_map):
    # type: (dict[str, Graph]) -> dict[str, EffectInfo]
    state = _EffectComputationState()
    return state.analyze_all(graph_map)
