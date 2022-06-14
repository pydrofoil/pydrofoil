from rpysail.parse import *
from rpysail.addtypes import *

import os

cir = os.path.join(os.path.dirname(__file__), "c.ir")

def test_parse_full():
    with open(cir, "rb") as f:
        s = f.read()
    res = parser.parse(lexer.lex(s))
    visitor = ResolveNamesVisitor()
    res.visit(visitor)
    assert visitor.names['zjump'] # exists
    assert visitor.names['zJGT'].value == 1
    assert visitor.names['zAINST'] # exists
    assert visitor.names['zsail_mask'].value is not None
    assert visitor.names['zcompute_value'].value.localtypes['zashadowz31_lz30'].typ.name == "%bv16"
    assert visitor.names['zcompute_value'].value.localtypes['za'].typ.name == "%bv1"

