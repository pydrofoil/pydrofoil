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
    assert visitor.names['zjum'] # exists
    assert visitor.names['zJGT'].value == 2
    assert visitor.names['zAINST'] # exists

