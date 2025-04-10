import z3
from pydrofoil import ir

class Value(object):
    pass

class Constant(Value):
    
    def __init__(self, val):
        self.value = val

    def toz3(self):
        return int(self.value)
    
class Z3Value(Value):
    
    def __init__(self, val):
        self.value = val

    def toz3(self):
        return self.value


class Interpreter(object):

    fork_counter = 0
    
    def __init__(self, graph, args):
        self.graph = graph
        self.args = args
        self.forknum = Interpreter.fork_counter
        Interpreter.fork_counter += 1
        assert len(args) == len(graph.args)
        self.environment = {graph.args[i]:args[i] for i in range(len(args))} # assume args are either z3backend.Constant or z3backend.Z3Value
        assert not graph.has_loop

    def run(self, block=None):
        """ interpret a graph, either begin with graph.startblock or the block passed as arg """
        if block:
            cur_block = block
        else:
            cur_block = self.graph.startblock

        while True:
            for op in cur_block.operations:
                self.execute_op(op)
            
            next = cur_block.next
            self.prev_block = cur_block
            cur_block = self.execute_next(next)
            if not cur_block:
                break
        self._debug_print(("returns", block))
        return self.w_result
    
    def fork(self):
        """ create a copy of the interpreter """
        f_interp = Interpreter(self.graph, self.args)
        f_interp.environment = self.environment.copy()
        return f_interp

    def execute_next(self, next):
        """ get next block to execute, or set ret value and return None, or fork interpreter on non const cond. goto """
        if isinstance(next, ir.Goto):
            return next.target
        elif isinstance(next, ir.ConditionalGoto):
            w_cond = self.convert(next.booleanvalue)
            if isinstance(w_cond, Constant):
                if w_cond.value:
                    return next.truetarget
                return next.falsetarget
            else:
                # fork 
                interp1 = self.fork()
                interp2 = self.fork()
                w_res_true = interp1.run(next.truetarget)
                w_res_false = interp2.run(next.falsetarget)
                self.w_result = Z3Value(z3.If(w_cond.toz3(), w_res_true.toz3(), w_res_false.toz3()))
                return None
        elif isinstance(next, ir.Return):
            self.w_result = self.convert(next.value)
            return None # TODO: arg
        elif isinstance(next, ir.Raise):
            self.w_result = Z3Value(z3.BitVecVal(0, 64) == z3.BitVecVal(1, 64)) # raising an errer => False 
            return None
        else:
            assert 0, "implement %s" %str(next)
    
    def _debug_print(self, msg=""):
        print "interp_%s:" % self.forknum, msg
            
    def convert(self, arg):
        """ wrap an argument """
        if isinstance(arg, ir.SmallBitVectorConstant):
            w_arg = Constant(arg.value)
        elif isinstance(arg, ir.EnumConstant):
            # TODO:
            #self._debug_print((dir(arg), arg.variant))
            w_arg = Constant(arg)
        elif isinstance(arg, ir.Constant):
            assert 0
        else:
            w_arg = self.environment[arg]    
        return w_arg


    def getargs(self, op):
        """ get all wrapped args of an operation """
        res = []
        for arg in op.args:
            res.append(self.convert(arg))
        return res

    def execute_op(self, op):
        """ execute an opearion and write result into environment """
        if isinstance(op, ir.Phi):
            index = op.prevblocks.index(self.prev_block)
            result = self.convert(op.prevvalues[index])
            self.environment[op] = result
            return
        elif op.name == "@eq_bits_bv_bv":
            arg0, arg1 = self.getargs(op)
            if isinstance(arg0, Constant) and isinstance(arg1, Constant):
                result = Constant(arg0.value == arg1.value)
            else:
                result = Z3Value(arg0.toz3() == arg1.toz3())
            self.environment[op] = result
            return
        assert 0 
