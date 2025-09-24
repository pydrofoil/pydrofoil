import collections

from pydrofoil import ir


class MockCodegen(object):
    builtin_names = {
        "zz5izDzKz5i64": "int_to_int64",
        "zz5i64zDzKz5i": "int64_to_int",
    }

    def __init__(self, graphs, entry_points=None):
        # type: (dict[str, ir.Graph], list[str] | None) -> None
        self.all_graph_by_name = graphs
        self.inlinable_functions = {}
        self.inline_dependencies = collections.defaultdict(set)
        self.method_graphs_by_name = {}
        self.program_entrypoints = entry_points

    def get_effects(self, _):
        pass

    def print_debug_msg(self, _):
        pass

    def add_graph(self, graph, emit_function=None, *args, **kwargs):
        self.all_graph_by_name[graph.name] = graph
