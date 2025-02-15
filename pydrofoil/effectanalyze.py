from pydrofoil import parse, types, binaryop, operations, supportcode, bitvector
from collections import defaultdict, deque

class EffectLattice(object):
    def __init__(self, reads, writes, prims):
        if reads is None:
            self.reads = self.writes = self.prims = None
            return
        self.reads = frozenset(reads)
        self.writes = frozenset(writes)
        self.prims = frozenset(prims)

    def join(self, other):
        if self.is_top() or other.is_top():
            return EffectLattice.top
        return EffectLattice(self.reads.union(other.reads),
                             self.writes.union(other.writes),
                             self.prims.union(other.prims))

    def is_above(self, other):
        if self.is_top():
            return True
        if other.is_top():
            return False
        if other.is_bottom():
            return True
        return (self.reads.issuperset(other.reads) and
                self.writes.issuperset(other.writes) and
                self.prims.issuperset(other.prims))

    def is_top(self):
        return self.reads is None

    def is_bottom(self):
        return not self.reads and not self.writes and not self.prims

    def __eq__(self, other):
        return (self.reads, self.writes, self.prims) == (other.reads, other.writes, other.prims)

    def __ne__(self, other):
        return not self == other

    def __repr__(self):
        if self.reads is None:
            return "EffectLattice.top"
        if self.is_bottom():
            return "EffectLattice.bottom"
        return "EffectLattice(%r, %r, %r)" % (self.reads, self.writes, self.prims)

EffectLattice.bottom = EffectLattice((), (), ())
EffectLattice.top = EffectLattice(None, None, None)


class ReadWriteAnalyzer(object):
    def __init__(self, codegen):
        self.codegen = codegen
        self.func_effects = {} # name -> EffectLattice
        self.callers_of_graphs = defaultdict(set) # graph -> set of graphs

    def analyze_all(self):
        todo = deque(self.codegen.all_graph_by_name.values())
        for meth_graphs in self.codegen.method_graphs_by_name.values():
            todo.extend(meth_graphs.values())
        while todo:
            graph = todo.popleft()
            newres = self.analyze_graph(graph)
            oldres = self.func_effects.get(graph.name, EffectLattice.bottom)
            if newres != oldres:
                print graph.name, newres, len(todo)
                assert newres.is_above(oldres)
                self.func_effects[graph.name] = newres
                todo.extend(self.callers_of_graphs[graph])
        self.print_callgraph()
        print "---"
        for name in sorted({x for e in self.func_effects.values() for x in e.prims}):
            print name
        import pdb;pdb.set_trace()

    def print_callgraph(self):
        for callee, callers in self.callers_of_graphs.iteritems():
            print callee.name, self.func_effects.get(callee.name, EffectLattice.bottom)
            for caller in callers:
                print "    ", caller.name

    def analyze_graph(self, graph):
        self.current_graph = graph
        result = EffectLattice.bottom
        for block in graph.iterblocks():
            for op in block.operations:
                meth = getattr(self, "analyze_" + op.__class__.__name__, self.analyze_default)
                opres = meth(op)
                result = result.join(opres)
        self.current_graph = None
        return result

    def _builtinname(self, name):
        return self.codegen.builtin_names.get(name, name)

    def analyze_default(self, op):
        if not op.can_have_side_effects:
            return EffectLattice.bottom
        import pdb;pdb.set_trace()
        return EffectLattice.top

    def analyze_FieldWrite(self, op):
        return EffectLattice.bottom # for now

    def analyze_Operation(self, op):
        name = self._builtinname(op.name)
        if name in self.codegen.all_graph_by_name:
            return self.analyze_call(op, self.codegen.all_graph_by_name[name])
        if name in self.codegen.method_graphs_by_name:
            result = EffectLattice.bottom
            for callee in self.codegen.method_graphs_by_name[name].values():
                result = result.join(self.analyze_call(op, callee))
            return result
        if name.lstrip('@').lstrip("$") in supportcode.purefunctions:
            return EffectLattice.bottom
        if op.is_union_creation():
            return EffectLattice.bottom
        if name in {'@not', '@addi', '@subi', 'eq_bool'}:
            return EffectLattice.bottom
        return EffectLattice((), (), [name])

    def analyze_call(self, op, callee):
        self.callers_of_graphs[callee].add(self.current_graph)
        return self.func_effects.get(callee.name, EffectLattice.bottom)

    def analyze_GlobalWrite(self, op):
        return EffectLattice((), [op.name], ())

    def analyze_GlobalRead(self, op):
        return EffectLattice([op.name], (), ())

    def analyze_Comment(self, op):
        return EffectLattice.bottom



def analyze_all(codegen):
    rwa = ReadWriteAnalyzer(codegen)
    rwa.analyze_all()

