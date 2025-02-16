import os

from pydrofoil import parse
from pydrofoil.makecode import Codegen
from pydrofoil.effectanalyze import analyze_all, EffectLattice

thisdir = os.path.dirname(__file__)
cir = os.path.join(thisdir, "nand2tetris/generated/nand2tetris.jib")


def analyze(s, support_code):
    from pydrofoil.infer import infer

    ast = parse.parser.parse(parse.lexer.lex(s))
    context = infer(ast)
    c = Codegen()
    ast.make_code(c)
    return analyze_all(c)
    import pdb

    pdb.set_trace()


def test_analyze_nand():
    import py
    from pydrofoil.test.nand2tetris import supportcodenand
    from rpython.translator.interactive import Translation

    with open(cir, "rb") as f:
        s = f.read()
    support_code = (
        "from pydrofoil.test.nand2tetris import supportcodenand as supportcode"
    )
    rwa = analyze(s, support_code)
    allregs = frozenset(["zA", "zD", "zPC"])
    allprims = frozenset(
        ["my_print_debug", "my_read_rom", "my_read_mem", "my_write_mem"]
    )
    nand_top = EffectLattice(allregs, allregs, allprims)
    assert rwa.func_effects == {
        "zassign_dest": EffectLattice(
            frozenset(["zA"]), frozenset(["zA", "zD"]), frozenset(["my_write_mem"])
        ),
        "zcompute_value": EffectLattice(
            frozenset(["zA", "zD"]), frozenset([]), frozenset(["my_read_mem"])
        ),
        "zexecute_zAINST": EffectLattice(
            frozenset(["zPC"]), frozenset(["zA", "zPC"]), frozenset([])
        ),
        "zexecute_zCINST": EffectLattice(
            allregs, allregs, frozenset(["my_read_mem", "my_write_mem"])
        ),
        "zfetch_decode_execute": EffectLattice(
            allregs, allregs, frozenset(["my_read_mem", "my_read_rom", "my_write_mem"])
        ),
        "zinitializze_registers": EffectLattice(
            frozenset([]), frozenset(["zPC", "zA", "zD"]), frozenset([])
        ),
        "zmain": nand_top,
        "zmaybe_jump": EffectLattice(
            frozenset(["zPC", "zA"]), frozenset(["zPC"]), frozenset([])
        ),
        "zmymain": nand_top,
        "zrun": nand_top,
    }
