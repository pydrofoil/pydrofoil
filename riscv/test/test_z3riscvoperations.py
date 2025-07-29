import pytest
import z3
import os
from pydrofoil import bitvector, ir, types
from pydrofoil.types import *
from pydrofoil import graphalgorithms
from pydrofoil.z3backend import z3backend, z3btypes

from hypothesis import given, strategies, assume, example, settings

from rpython.rlib.rarithmetic import r_uint
from rpython.rlib.rbigint import rbigint

### copied from test_z3riscv.py ###

@pytest.fixture(scope='session')
def riscv_first_shared_state():
    from riscv import targetriscv
    pf = os.path.join(os.path.dirname(os.path.abspath(targetriscv.__file__)), "generated", "riscvgraphs_functions.py")
    pm = os.path.join(os.path.dirname(os.path.abspath(targetriscv.__file__)), "generated", "riscvgraphs_methods.py")
    if not os.path.exists(pf) or not os.path.exists(pm): 
        print "generating graphs"
        c = targetriscv.make_codegen()
        s = dump_graphs_and_registers(c)
        with open(pf, "w") as f:
            f.write(s)
        s = dump_methods(c)
        with open(pm, "w") as f:
            f.write(s)
    import time
    t1 = time.time()
    from riscv.generated import riscvgraphs_functions, riscvgraphs_methods
    riscvsharedstate = z3backend.SharedState(
        {name: func() for name, func in riscvgraphs_functions.funcs.iteritems()},
        riscvgraphs_functions.registers,
        {name: {mname: mthd() for mname, mthd in mthds.iteritems()} for name, mthds in riscvgraphs_methods.mthds.iteritems()},
    )
    ### We assume that every graph only has one return; thus we must compute every singe return graph here ### 
    for name, graph in riscvsharedstate.funcs.iteritems():
        riscvsharedstate.funcs[name] = graphalgorithms.compute_single_return_graph(graph)
    for name, graphs in riscvsharedstate.mthds.iteritems():
        for mname, graph in graphs.iteritems():
            riscvsharedstate.mthds[name][mname] = graphalgorithms.compute_single_return_graph(graph)
    t2 = time.time()
    print "loaded in %ss" % round(t2 - t1, 2)
    return riscvsharedstate

def dump_methods(c):
    code = ["from pydrofoil.ir import *",
            "from pydrofoil.types import *",
            "mthds = {}"]
    for name, graphs in c.method_graphs_by_name.iteritems():
        code.append("%s_methods = {}" % name)
        for m_name, graph in graphs.iteritems():
            if m_name == None:
                m_name = "___default___" # TODO: is this naming ok?
            code.append("def %s():" % m_name)
            for line in ir.print_graph_construction(graph):
                code.append("    " + line)
            code.append("    return graph")
            code.append("%s_methods[%r] = %s" % (name, m_name, m_name))
        code.append("mthds[%r] = %s_methods" % (name, name))
        code.append("")
    return "\n".join(code)


def dump_graphs_and_registers(c):
    code = ["from pydrofoil.ir import *",
            "from pydrofoil.types import *",
            "funcs = {}"]
    for name, graph in c.all_graph_by_name.iteritems():
        code.append("def %s():" % name)
        for line in ir.print_graph_construction(graph):
            code.append("    " + line)
        code.append("    return graph")
        code.append("funcs[%r] = %s" % (name, name))
        code.append("")
    registers = {name: c.globalnames[name].typ for name in c.all_registers}
    code.append("registers = {}")
    for name, typ in registers.iteritems():
        code.append("registers[%r] = %s" % (name, typ))
    return "\n".join(code)

@pytest.fixture(scope='session')
def abs_zast_session(riscv_first_shared_state):
    bv = z3.BitVec("z3mergevar", 32)
    return z3backend.RiscvInterpreter(riscv_first_shared_state.funcs["zencdec_backwards"], [z3btypes.Z3Value(bv)],
                                       riscv_first_shared_state.copy()).run(), bv

@pytest.fixture(scope='function')
def abs_zast(abs_zast_session):
    zast, bv = abs_zast_session
    return z3btypes.Z3Value(zast.toz3()), bv # z3 refs are immuatable

@pytest.fixture(scope='function')
def riscvsharedstate(riscv_first_shared_state):
    return riscv_first_shared_state.copy()

## copied from test_supportcode.py ##

def _make_small_bitvector(data):
    width = data.draw(strategies.integers(1, 64))
    value = data.draw(strategies.integers(0, 2**width-1))
    return ir.SmallBitVectorConstant.from_ruint(width, r_uint(value))


def _make_small_bitvector_2(data):
    width = data.draw(strategies.integers(2, 64))
    value = data.draw(strategies.integers(0, 2**width-1))
    return ir.SmallBitVectorConstant.from_ruint(width, r_uint(value))

def _make_generic_bitvector(data):
    width = data.draw(strategies.integers(65, 1000))
    value = data.draw(strategies.integers(0, 2**width-1))
    return ir.GenericBitVectorConstant(rbigint.fromlong(value))

def _make_2_small_bitvectors_w_le_64(data):
    width0 = data.draw(strategies.integers(1, 63))
    value0 = data.draw(strategies.integers(1, 2**width0-1))
    width1 = data.draw(strategies.integers(1, 64-width0))
    value1 = data.draw(strategies.integers(0, 2**width1-1))
    return (ir.SmallBitVectorConstant.from_ruint(width0, r_uint(value0)), ir.SmallBitVectorConstant.from_ruint(width1, r_uint(value1)))

def _make_rv64_li_params(data):
    imm = data.draw(strategies.integers(1, 2**12-1))
    dest_reg_num = data.draw(strategies.integers(1, 2**5-1))
    return (ir.SmallBitVectorConstant.from_ruint(12, r_uint(imm)), ir.SmallBitVectorConstant.from_ruint(5, r_uint(dest_reg_num)))

small_bitvectors = strategies.builds(
    _make_small_bitvector,
    strategies.data())

small_bitvectors_w_ge_2 = strategies.builds(
    _make_small_bitvector_2,
    strategies.data())

small_bitvector_2tuple_w_le_64 = strategies.builds(
    _make_2_small_bitvectors_w_le_64,
    strategies.data())

generic_bitvectors = strategies.builds(
    _make_generic_bitvector,
    strategies.data())

li_params = strategies.builds(
    _make_rv64_li_params,
    strategies.data()
)

#####################################

class DummyGraph():

    def __init__(self):
        self.has_loop = False
        self.args = []
    
DummyGraph.Dummy = DummyGraph()

#####################################

def test_sign_error(riscvsharedstate, abs_zast):
    li_params = (ir.SmallBitVectorConstant(0x801, SmallFixedBitVector(12)), ir.SmallBitVectorConstant(0b1, SmallFixedBitVector(5))) # 801

    zast, bv_zast = abs_zast

    graph = riscvsharedstate.funcs["zexecute_zITYPE"]
    interp = z3backend.RiscvInterpreter(graph, [zast], riscvsharedstate)# interp must be init correctly
    # TODO: introduce new constructor for using it just for func calls like in executor ...

    init_memory = interp.memory

    w_res, call_mem, call_regs = interp._func_call(graph, [zast])

    res_reg = call_regs["zx%d" % li_params[1].value]

    assert isinstance(w_res, z3btypes.Enum)
    assert w_res.variant == "zRETIRE_SUCCESS"
    assert isinstance(res_reg, z3btypes.Z3Value)

    # immediate, src, func, dest ~ bv12 bv5, bv5, iop

    #000000000001 10001 000 10001 0010011
    #immm         src   iop dest  op? 
    #imm12 00000 000? dest5 

    src_reg = 0
    immediate = li_params[0].value


    # immediate can be negative
    # we must interpret immediate bits as signed bv
    if 2048 & immediate != 0:
        immediate = -(2**(12-1) - int(immediate & ~(2**(12-1)))) 
    else:
        immediate = int(immediate)


    dest_reg = li_params[1].value

    sanity = z3.BitVec("sanity ast", 32)

    solver = z3.Solver()

    solver.add(z3.Extract(31, 20, bv_zast) == z3.BitVecVal(immediate, 12)) # 31,  20
    sanity = z3.Concat(z3.BitVecVal(immediate, 12),  z3.Extract(19,0, sanity))

    solver.add(z3.Extract(19, 15, bv_zast) == z3.BitVecVal(src_reg, 5)) # 19, 15
    sanity = z3.Concat(z3.Extract(31, 20, sanity), z3.Concat(z3.BitVecVal(src_reg, 5),  z3.Extract(14,0, sanity)))

    solver.add(z3.Extract(14, 12, bv_zast) == z3.BitVecVal(0, 3)) # addi 14,  12
    sanity = z3.Concat(z3.Extract(31, 15, sanity),z3.Concat(z3.BitVecVal(0, 3),  z3.Extract(11,0, sanity)))

    solver.add(z3.Extract(11, 7, bv_zast) == z3.BitVecVal(dest_reg, 5)) # 11, 7
    sanity = z3.Concat(z3.Extract(31, 12, sanity),z3.Concat(z3.BitVecVal(dest_reg, 5),  z3.Extract(6,0, sanity)))

    solver.add(z3.Extract(6, 0, bv_zast) == z3.BitVecVal(0b0010011, 7)) # addi  6, 0
    sanity = z3.Concat(z3.Extract(31, 7, sanity), z3.BitVecVal(0b0010011, 7))

    assert solver.check(z3.Not(bv_zast == z3.BitVecVal(0b10000000000100000000000010010011,32))) == z3.unsat

    # z3.simplify(z3.substitute(res_reg.toz3(), (bv_zast, z3.BitVecVal(0b10000000000100000000000010010011,32))))
    print "target reg  is %s" % str(li_params[1])
    print z3.simplify(z3.substitute(res_reg.toz3(), (bv_zast, z3.BitVecVal(0b10000000000100000000000010010011,32))))
    #for num in range(1,31):
    #    print z3.simplify(z3.substitute(call_regs["zx"+str(num)].toz3(), (bv_zast, z3.BitVecVal(0b10000000000100000000000010010011,32))))
    solvable = solver.check(z3.Not(immediate == res_reg.toz3()))
    

    # res depends on misa, mstatus and cur_privilege
    #assert solvable == z3.unsat

    assert isinstance(interp.w_raises, z3btypes.Z3Value)
    assert interp.memory == init_memory


@settings(deadline=None)
@given(li_params)
def test_func_call_rv64_li(riscvsharedstate, abs_zast, li_params):

    zast, bv_zast = abs_zast

    graph = riscvsharedstate.funcs["zexecute_zITYPE"]
    interp = z3backend.RiscvInterpreter(graph, [zast], riscvsharedstate)# interp must be init correctly
    # TODO: introduce new constructor for using it just for func calls like in executor ...

    init_memory = interp.memory

    w_res, call_mem, call_regs = interp._func_call(graph, [zast])


    res_reg = call_regs["zx%d" % li_params[1].value]

    assert isinstance(w_res, z3btypes.Enum)
    assert w_res.variant == "zRETIRE_SUCCESS"
    assert isinstance(res_reg, z3btypes.Z3Value)
    src_reg = 0
    immediate = li_params[0].value

    # immediate can be negative
    # we must interpret immediate bits as signed bv
    if 2048 & immediate != 0:
        immediate = -(2**(12-1) - int(immediate & ~(2**(12-1)))) 
    else:
        immediate = int(immediate)

    dest_reg = li_params[1].value

    solver = z3.Solver()
    solver.add(z3.Extract(31, 20, bv_zast) == z3.BitVecVal(immediate, 12)) # 31,  20
    solver.add(z3.Extract(19, 15, bv_zast) == z3.BitVecVal(src_reg, 5)) # 19, 15
    solver.add(z3.Extract(14, 12, bv_zast) == z3.BitVecVal(0, 3)) # addi 14,  12
    solver.add(z3.Extract(11, 7, bv_zast) == z3.BitVecVal(dest_reg, 5)) # 11, 7
    solver.add(z3.Extract(6, 0, bv_zast) == z3.BitVecVal(0b0010011, 7)) # addi  6, 0
    solvable = solver.check(z3.Not(immediate == res_reg.toz3()))
    assert solvable == z3.unsat

    assert isinstance(interp.w_raises, z3btypes.Z3Value)
    assert interp.memory == init_memory

@settings(deadline=None)
@given(li_params)
def test_method_call_rv64_li(riscvsharedstate, abs_zast, li_params):

    zast, bv_zast = abs_zast

    interp = z3backend.RiscvInterpreter(riscvsharedstate.funcs["zexecute_zITYPE"], [zast], riscvsharedstate)# interp must be init correctly

    init_memory = interp.memory

    graphs = riscvsharedstate.mthds["zexecute"] # zassembly_forwards_methods['zITYPE']

    graph = graphs["zITYPE"]

    w_res, call_mem, call_regs = interp._method_call(graph, [zast])


    res_reg = call_regs["zx%d" % li_params[1].value]

    assert isinstance(w_res, z3btypes.Enum)
    assert w_res.variant == "zRETIRE_SUCCESS"
    assert isinstance(res_reg, z3btypes.Z3Value)
    src_reg = 0
    immediate = li_params[0].value

    # immediate can be negative
    # we must interpret immediate bits as signed bv
    if 2048 & immediate != 0:
        immediate = -(2**(12-1) - int(immediate & ~(2**(12-1)))) 
    else:
        immediate = int(immediate)

    dest_reg = li_params[1].value

    solver = z3.Solver()
    solver.add(z3.Extract(31, 20, bv_zast) == z3.BitVecVal(immediate, 12)) # 31,  20
    solver.add(z3.Extract(19, 15, bv_zast) == z3.BitVecVal(src_reg, 5)) # 19, 15
    solver.add(z3.Extract(14, 12, bv_zast) == z3.BitVecVal(0, 3)) # addi 14,  12
    solver.add(z3.Extract(11, 7, bv_zast) == z3.BitVecVal(dest_reg, 5)) # 11, 7
    solver.add(z3.Extract(6, 0, bv_zast) == z3.BitVecVal(0b0010011, 7)) # addi  6, 0
    solvable = solver.check(z3.Not(immediate == res_reg.toz3()))
    assert solvable == z3.unsat

    assert isinstance(interp.w_raises, z3btypes.Z3Value)
    assert interp.memory == init_memory