from rpython.tool.pairtype import extendabletype

def unique(cls):
    instances = {}
    def __new__(cls, *args):
        res = instances.get(args, None)
        if res is not None:
            return res
        res = object.__new__(cls, *args)
        instances[args] = res
        return res
    cls.__new__ = staticmethod(__new__)
    return cls

def singleton(cls):
    cls._INSTANCE = cls()

    def __new__(cls):
        return cls._INSTANCE
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
    def __init__(self, name, names, typs):
        self.name = name
        self.convert_to_pypy = 'convert_to_pypy_%s' % name
        self.convert_from_pypy = 'convert_from_pypy_%s' % name
        self.names = names
        self.typs = typs
        assert len(self.names) == len(self.typs)
        self.variants = {}
        for name, typ in zip(names, typs):
            self.variants[name] = typ

    def __repr__(self):
        return "%s(%r, %s, %s)" % (type(self).__name__, self.name, self.names, self.typs)


@unique
class Enum(Type):
    uninitialized_value = '-1'

    def __init__(self, name, elements):
        self.name = name
        self.elements = elements

    def sail_repr(self):
        return "enum %s" % (self.name.lstrip('z'), )

    def __repr__(self):
        return "%s(%r, %r)" % (type(self).__name__, self.name, self.elements)


@unique
class Struct(Type):
    def __init__(self, name, names, typs, tuplestruct=False):
        assert isinstance(name, str)
        self.name = name
        self.names = names
        self.typs = typs
        self.fieldtyps = {}
        assert len(names) == len(typs)
        for name, typ in zip(names, typs):
            self.fieldtyps[name] = typ
        self.tuplestruct = tuplestruct

    def sail_repr(self):
        from pydrofoil.mangle import demangle
        if len(self.names) == 1 and isinstance(self.fieldtyps[self.names[0]], SmallFixedBitVector):
            return "bitfield %s" % demangle(self.name)
        if self.tuplestruct:
            return '(%s)' % (", ".join([typ.sail_repr() for typ in self.typs]), )
        return Type.sail_repr(self)

    def __repr__(self):
        extra = ''
        if self.tuplestruct:
            extra = ', True'
        return "%s(%r, %r, %r%s)" % (type(self).__name__, self.name, self.names, self.typs, extra)

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

    def sail_repr(self):
        return "vector(?, %s)" % (self.typ.sail_repr(), )

    def __repr__(self):
        return "%s(%r)" % (type(self).__name__, self.typ)

@unique
class FVec(Type):
    uninitialized_value = 'None'

    def __init__(self, number, typ):
        assert isinstance(typ, Type)
        self.number = number
        self.typ = typ

    def sail_repr(self):
        return "vector(%s, %s)" % (self.number, self.typ.sail_repr())

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

@singleton
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
        assert 0 <= width <= 64
        self.width = width
        self.convert_to_pypy = "supportcode.generate_convert_to_pypy_bitvector_ruint(%s)" % width
        self.convert_from_pypy = "supportcode.generate_convert_from_pypy_bitvector_ruint(%s)" % width

    def sail_repr(self):
        return "bits(%s)" % (self.width, )

    def __repr__(self):
        return "%s(%s)" % (type(self).__name__, self.width)


@unique
class BigFixedBitVector(Type):

    def __init__(self, width):
        # size known at compile time
        assert width > 64
        self.width = width
        self.uninitialized_value = "bitvector.SparseBitVector(%s, r_uint(0))" % width

    def sail_repr(self):
        return "bits(%s)" % (self.width, )

    def __repr__(self):
        return "BigFixedBitVector(%s)" % (self.width, )


@singleton
class GenericBitVector(Type):
    uninitialized_value = "bitvector.UNITIALIZED_BV"

    def sail_repr(self):
        return 'bits(?)'

    def __repr__(self):
        return "%s()" % (type(self).__name__, )

@singleton
class MachineInt(Type):
    uninitialized_value = "-0xfefe"

    def sail_repr(self):
        return 'int'

    def __repr__(self):
        return "%s()" % (type(self).__name__, )

@singleton
class Int(Type):
    uninitialized_value = "UninitInt"

    def __repr__(self):
        return "%s()" % (type(self).__name__, )

@singleton
class Bool(Type):
    uninitialized_value = "False"
    convert_to_pypy = "supportcode.convert_to_pypy_bool"
    convert_from_pypy = "supportcode.convert_from_pypy_bool"

    def __repr__(self):
        return "%s()" % (type(self).__name__, )

    def sail_repr(self):
        return 'bool'

@singleton
class Unit(Type):
    uninitialized_value = "()"
    convert_to_pypy = "supportcode.convert_to_pypy_unit"
    convert_from_pypy = "supportcode.convert_from_pypy_unit"

    def sail_repr(self):
        return 'unit'

    def __repr__(self):
        return "%s()" % (type(self).__name__, )

Bit = lambda : SmallFixedBitVector(1)

@singleton
class String(Type):
    uninitialized_value = "None"
    convert_to_pypy = "supportcode.convert_to_pypy_string"
    convert_from_pypy = "supportcode.convert_from_pypy_string"

    def sail_repr(self):
        return 'string'

    def __repr__(self):
        return "%s()" % (type(self).__name__, )

@singleton
class Real(Type):
    uninitialized_value = "None"

    def sail_repr(self):
        return 'real'

    def __repr__(self):
        return "%s()" % (type(self).__name__, )
