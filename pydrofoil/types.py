from rpython.tool.pairtype import extendabletype

def unique(cls):
    instances = {}
    def __new__(cls, *args):
        if args in instances:
            return instances[args]
        res = object.__new__(cls, *args)
        instances[args] = res
        return res
    cls.__new__ = staticmethod(__new__)
    return cls

class Type(object):
    __metaclass__ = extendabletype
    uninitialized_value = '"uninitialized_value"' # often fine for rpython!

@unique
class Union(Type):
    def __init__(self, ast):
        self.ast = ast

@unique
class Enum(Type):
    def __init__(self, ast):
        self.ast = ast

@unique
class Struct(Type):
    def __init__(self, ast):
        self.ast = ast

@unique
class Ref(Type):
    def __init__(self, typ):
        assert isinstance(typ, Type)
        self.typ = typ

@unique
class Vec(Type):
    def __init__(self, typ):
        assert isinstance(typ, Type)
        self.typ = typ

@unique
class Function(Type):
    def __init__(self, argtype, restype):
        assert isinstance(argtype, Type)
        assert isinstance(restype, Type)
        self.argtype = argtype
        self.restype = restype

@unique
class Tuple(Type):
    def __init__(self, elements):
        self.elements = elements

@unique
class List(Type):
    # a linked list
    uninitialized_value = "None"

    def __init__(self, typ):
        assert isinstance(typ, Type)
        self.typ = typ

@unique
class FixedBitVector(Type):
    uninitialized_value = "r_uint(0)"

    def __init__(self, width):
        # size known at compile time
        self.width = width

    def __repr__(self):
        return "FixedBitVector(%s)" % (self.width, )

@unique
class SmallBitVector(Type):
    uninitialized_value = "None"

    # small bitvector: length of at most width
    def __init__(self, width):
        self.width = width

    def __repr__(self):
        return "SmallBitVector(%s)" % (self.width, )

@unique
class GenericBitVector(Type):
    uninitialized_value = "None"

@unique
class MachineInt(Type):
    uninitialized_value = "-0xfefe"

@unique
class Int(Type):
    uninitialized_value = "UninitInt"

@unique
class Bool(Type):
    uninitialized_value = "False"

@unique
class Unit(Type):
    uninitialized_value = "()"

@unique
class Bit(Type):
    uninitialized_value = "r_uint(0)"

@unique
class String(Type):
    uninitialized_value = "None"
