import pytest

from pydrofoil import parse
from pydrofoil.emitfunction import identify_safe_structs
from pydrofoil.types import *
from pydrofoil.ir import *


def test_identify_mutated_structs():
    zAccess_kindzIUarm_acc_typezIzKzK = Union('zAccess_kindzIUarm_acc_typezIzKzK', ('zAK_archzIUarm_acc_typezIzKzK', 'zAK_explicitzIUarm_acc_typezIzKzK', 'zAK_ifetchzIUarm_acc_typezIzKzK', 'zAK_ttwzIUarm_acc_typezIzKzK'), (Union('zarm_acc_type', ('zSAcc_ASIMD', 'zSAcc_AT', 'zSAcc_DC', 'zSAcc_DCZero', 'zSAcc_GCS', 'zSAcc_GPTW', 'zSAcc_IC', 'zSAcc_NV2', 'zSAcc_SME', 'zSAcc_SPE', 'zSAcc_SVE'), (Bool(), Unit(), Unit(), Unit(), Unit(), Unit(), Unit(), Unit(), Bool(), Unit(), Bool())), Struct('zExplicit_access_kind', ('zstrength', 'zvariety'), (Enum('zAccess_strength', ('zAS_normal', 'zAS_rel_or_acq', 'zAS_acq_rcpc')), Enum('zAccess_variety', ('zAV_plain', 'zAV_exclusive', 'zAV_atomic_rmw')))), Unit(), Unit()))
    structtyp = Struct('zMem_read_requestzIUarm_acc_typezIzKzCbzCOzIRTranslationInfozKzK', ('zaccess_kind', 'zpa', 'zsizze', 'ztag', 'zva'), (zAccess_kindzIUarm_acc_typezIzKzK, GenericBitVector(), Int(), Bool(), Union('zoptionzIbzK', ('zNonezIbzK', 'zSomezIbzK'), (Unit(), GenericBitVector()))))
    zrequest = Argument('zrequest', structtyp)
    block0 = Block()
    i1 = block0.emit(FieldAccess, 'zaccess_kind', [zrequest], zAccess_kindzIUarm_acc_typezIzKzK, None, None)
    block0.next = Return(i1, None)
    graph = Graph('g', [zrequest], block0)
    assert identify_safe_structs(graph) == {structtyp}

    zrequest = Argument('zrequest', structtyp)
    block0 = Block()
    i1 = block0.emit(FieldWrite, 'zsizze', [zrequest, IntConstant(15)], Unit(), None, None)
    block0.next = Return(i1, None)
    graph = Graph('g', [zrequest], block0)
    assert identify_safe_structs(graph) == set()
