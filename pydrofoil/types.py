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
class FixedBitVector(Type):
    def __init__(self, width):
        # size known at compile time
        self.width = width

    def __repr__(self):
        return "FixedBitVector(%s)" % (self.width, )

@unique
class SmallBitVector(Type):
    # small bitvector: length of at most width
    def __init__(self, width):
        self.width = width

    def __repr__(self):
        return "SmallBitVector(%s)" % (self.width, )

@unique
class GenericBitVector(Type):
    pass

@unique
class MachineInt(Type):
    pass

@unique
class Int(Type):
    pass

@unique
class Bool(Type):
    pass

@unique
class Unit(Type):
    pass

@unique
class Bit(Type):
    pass

@unique
class String(Type):
    pass
