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

    convert_to_pypy = "supportcode.convert_to_pypy_error"
    convert_from_pypy = "supportcode.convert_from_pypy_error"

    def sail_repr(self):
        return repr(self)


@unique
class Union(Type):
    def __init__(self, ast):
        self.ast = ast

    def __repr__(self):
        return "%s(<%s>)" % (type(self).__name__, self.ast.name)

@unique
class Enum(Type):
    def __init__(self, ast):
        self.ast = ast

    def sail_repr(self):
        return "enum %s" % (self.ast.name.lstrip('z'), )

    def __repr__(self):
        return "%s(<%s>)" % (type(self).__name__, self.ast.name)

@unique
class Struct(Type):
    def __init__(self, ast):
        self.ast = ast

    def sail_repr(self):
        ast = self.ast
        if len(ast.names) == 1 and isinstance(self.fieldtyps[ast.names[0]], SmallFixedBitVector):
            return "bitfield %s" % self.ast.name.lstrip('z')
        return Type(sail_repr(self), )

    def __repr__(self):
        return "%s(<%s>)" % (type(self).__name__, self.ast.name)

@unique
class Ref(Type):
    def __init__(self, typ):
        assert isinstance(typ, Type)
        self.typ = typ

    def __repr__(self):
        return "%s(%r)" % (type(self).__name__, self.typ)

@unique
class Vec(Type):
    def __init__(self, typ):
        assert isinstance(typ, Type)
        self.typ = typ

    def __repr__(self):
        return "%s(%r)" % (type(self).__name__, self.typ)

@unique
class FVec(Type):
    def __init__(self, number, typ):
        assert isinstance(typ, Type)
        self.number = number
        self.typ = typ

    def __repr__(self):
        return "%s(%s, %r)" % (type(self).__name__, self.number, self.typ)

@unique
class Function(Type):
    def __init__(self, argtype, restype):
        assert isinstance(argtype, Type)
        assert isinstance(restype, Type)
        self.argtype = argtype
        self.restype = restype

    def __repr__(self):
        return "%s(%s, %r)" % (type(self).__name__, self.argtype, self.restype)

@unique
class Tuple(Type):
    def __init__(self, elements):
        self.elements = elements

    def __repr__(self):
        return "%s(%r)" % (type(self).__name__, self.elements)


@unique
class List(Type):
    # a linked list
    uninitialized_value = "None"

    def __init__(self, typ):
        assert isinstance(typ, Type)
        self.typ = typ

    def __repr__(self):
        return "%s(%r)" % (type(self).__name__, self.typ)

@unique
class NullType(Type):
    uninitialized_value = "None"

    def __init__(self):
        pass

    def __repr__(self):
        return "%s()" % (type(self).__name__, )

@unique
class SmallFixedBitVector(Type):
    uninitialized_value = "r_uint(0)"

    def __init__(self, width):
        # size known at compile time
        assert width <= 64
        self.width = width
        self.convert_to_pypy = "supportcode.generate_convert_to_pypy_bitvector_ruint(%s)" % width
        self.convert_from_pypy = "supportcode.generate_convert_from_pypy_bitvector_ruint(%s)" % width

    def sail_repr(self):
        return "bits(%s)" % (self.width, )

    def __repr__(self):
        return "%s(%s)" % (type(self).__name__, self.width)


@unique
class BigFixedBitVector(Type):
    uninitialized_value = "rbigint.fromint(0)"

    def __init__(self, width):
        # size known at compile time
        assert width > 64
        self.width = width

    def __repr__(self):
        return "BigFixedBitVector(%s)" % (self.width, )


@unique
class GenericBitVector(Type):
    uninitialized_value = "None"

    def __repr__(self):
        return "%s()" % (type(self).__name__, )

@unique
class MachineInt(Type):
    uninitialized_value = "-0xfefe"

    def __repr__(self):
        return "%s()" % (type(self).__name__, )

@unique
class Int(Type):
    uninitialized_value = "UninitInt"

    def __repr__(self):
        return "%s()" % (type(self).__name__, )

@unique
class Bool(Type):
    uninitialized_value = "False"
    convert_to_pypy = "supportcode.convert_to_pypy_bool"
    convert_from_pypy = "supportcode.convert_from_pypy_bool"

    def __repr__(self):
        return "%s()" % (type(self).__name__, )

    def sail_repr(self):
        return 'bool'

@unique
class Unit(Type):
    uninitialized_value = "()"

    def __repr__(self):
        return "%s()" % (type(self).__name__, )

@unique
class Bit(Type):
    uninitialized_value = "r_uint(0)"
    convert_to_pypy = "supportcode.generate_convert_to_pypy_bitvector_ruint(1)"
    convert_from_pypy = "supportcode.generate_convert_from_pypy_bitvector_ruint(1)"

    def __repr__(self):
        return "%s()" % (type(self).__name__, )

@unique
class String(Type):
    uninitialized_value = "None"

    def __repr__(self):
        return "%s()" % (type(self).__name__, )

@unique
class Real(Type):
    uninitialized_value = "None"

    def __repr__(self):
        return "%s()" % (type(self).__name__, )
