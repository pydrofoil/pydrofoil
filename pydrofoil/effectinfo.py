from pydrofoil.ir import GlobalRead, Graph, GlobalWrite

class EffectInfo(object):

    def __init__(self, register_reads=frozenset(), register_writes=frozenset()):
        self.register_reads = register_reads  # type: frozenset[str]
        self.register_writes = register_writes  # type: frozenset[str]

    def add_write(self, register_name):
        # type: (str) -> EffectInfo
        return EffectInfo(
            self.register_reads,
            self.register_writes | {register_name}
        )

    def add_read(self, register_name):
        # type: (str) -> EffectInfo
        return EffectInfo(
            self.register_reads | {register_name},
            self.register_writes,
        )

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