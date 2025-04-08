import pydrofoil.ir as ir
import z3

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
    
    def __init__(self, graph, args):
        self.graph = graph
        self.args = args
        assert len(args) == len(graph.args)
        self.environment = {graph.args[i]:args[i] for i in range(len(args))}
        assert not graph.has_loop

    def run(self, block=None):
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
        
        return self.w_result
    
    def fork(self):
        asert 0,

    def execute_next(self, next):
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
                return z3.If(w_cond, w_res_true, w_res_false)
        elif isinstance(next, ir.Return):
            self.w_result = self.convert(next.value)
            return None # TODO: arg
            
    def convert(self, arg):
        if isinstance(arg, ir.SmallBitVectorConstant):
            w_arg = Constant(arg.value)
        elif isinstance(arg, ir.EnumConstant):
            w_arg = Constant(arg)
        elif isinstance(arg, ir.Constant):
            assert 0
        else:
            w_arg = self.environment[arg]    
        return w_arg


    def getargs(self, op):
        res = []
        for arg in op.args:
            res.append(self.convert(arg))
        return res

    def execute_op(self, op):

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
