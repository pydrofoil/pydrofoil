from pydrofoil.parse import *
from pydrofoil.types import *
from pydrofoil.ir import *


def test_reconstruct():
    # smoke test to check whether the reconstruction code works
    zb = Argument('zb', SmallFixedBitVector(1))
    block0 = Block()
    block1 = Block()
    block2 = Block()
    block3 = Block()
    block4 = Block()
    block5 = Block()
    i1 = block0.emit(Cast, '$cast', [zb], GenericBitVector(), '`1 14:2-14:5', 'zz43')
    i2 = block0.emit(Cast, '$cast', [AstConstant(BitVectorConstant(constant='0b1', resolved_type=SmallFixedBitVector(1)), SmallFixedBitVector(1))], GenericBitVector(), '`1 14:2-14:5', 'zz44')
    i3 = block0.emit(Operation, 'zeq_bits', [i1, i2], Bool(), '`1 14:2-14:5', 'zz42')
    i4 = block0.emit(Operation, '@not', [i3], Bool(), '`1 13:27-16:1', None)
    block0.next = ConditionalGoto(i3, block1, block4, '`1 13:27-16:1')
    block1.next = Goto(block2, None)
    block2.next = Goto(block3, None)
    i5 = block3.emit_phi([block2, block5], [BooleanConstant.TRUE, BooleanConstant.FALSE], Bool())
    block3.next = Return(i5, None)
    block4.next = Goto(block5, None)
    block5.next = Goto(block3, None)
    graph = Graph('zbits1_to_bool', [zb], block0)

