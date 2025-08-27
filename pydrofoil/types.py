from pydrofoil.mangle import demangle
from pypy.interpreter.baseobjspace import W_Root

from rpython.tool.pairtype import extendabletype

def unique(cls):
    instances = {}
    base_new = cls.__new__
    def __new__(cls, *args):
        res = instances.get(args, None)
        if res is not None:
            return res
        res = base_new(cls, *args)
        instances[args] = res
        res.convert_to_pypy = "supportcode.generate_convert_to_pypy_error(%r)" % (cls.__name__ + str(id(res)))
        res.convert_from_pypy = "supportcode.generate_convert_from_pypy_error(%r)" % (cls.__name__ + str(id(res)))
        return res
    cls.__new__ = staticmethod(__new__)
    return cls

def singleton(cls):
    cls._INSTANCE = cls()
    if not hasattr(cls._INSTANCE, 'convert_to_pypy'):
        cls._INSTANCE.convert_to_pypy = "supportcode.generate_convert_to_pypy_error(%r)" % (cls.__name__ + str(id(cls._INSTANCE)))
    if not hasattr(cls._INSTANCE, 'convert_from_pypy'):
        cls._INSTANCE.convert_from_pypy = "supportcode.generate_convert_from_pypy_error(%r)" % (cls.__name__ + str(id(cls._INSTANCE)))

    def __new__(cls):
        return cls._INSTANCE
    cls.__new__ = staticmethod(__new__)

    return cls

class Type(W_Root):
    __metaclass__ = extendabletype
    uninitialized_value = '"uninitialized_value"' # often fine for rpython!

    def sail_repr(self):
        return repr(self)


@unique
class Union(Type):
    def __init__(self, name, names, typs):
        self.name = name
        self.demangled_name = demangle(name)
        self.convert_to_pypy = 'convert_to_pypy_%s' % name
        self.convert_from_pypy = 'convert_from_pypy_%s' % name
        self.names = names
        self.names_list = [demangle(name) for name in names]
        self.typs = typs
        self.typs_list = list(typs)
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
        self.demangled_name = demangle(name)
        self.elements = elements
        self.elements_list = [demangle(name) for name in elements]

    def sail_repr(self):
        return "enum %s" % (self.name.lstrip('z'), )

    def __repr__(self):
        return "%s(%r, %r)" % (type(self).__name__, self.name, self.elements)


@unique
class Struct(Type):
    def __new__(cls, name, names, typs, tuplestruct=False):
        if tuplestruct:
            cls = TupleStruct
        else:
            cls = RegularStruct
        return Type.__new__(cls, name, names, typs, tuplestruct)

    def __init__(self, name, names, typs, tuplestruct=False):
        assert type(self) is not Struct
        assert self.tuplestruct == tuplestruct
        assert isinstance(name, str)
        self.name = name # type: str
        self.demangled_name = demangle(name) # type: str
        self.names = names # type: tuple[str, ...]
        self.names_list = [demangle(name) for name in names]
        self.typs = typs # type: tuple[Type, ...]
        self.typs_list = list(typs) # type: list[Type]
        self.internaltyps = tuple((Packed(typ) if typ.packed_field_size else typ) for typ in typs)
        self.fieldtyps = {}
        self.internalfieldtyps = {}
        assert len(names) == len(typs)
        for name, typ, internaltyp in zip(names, self.typs, self.internaltyps):
            self.fieldtyps[name] = typ
            self.internalfieldtyps[name] = internaltyp
        self.tuplestruct = tuplestruct # type: bool

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
        return "Struct(%r, %r, %r%s)" % (self.name, self.names, self.typs, extra)

class RegularStruct(Struct):
    tuplestruct = False

class TupleStruct(Struct):
    tuplestruct = True

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
        self.convert_from_pypy = "supportcode.generate_convert_from_pypy_vec(%s)" % (typ.convert_from_pypy, )
        self.convert_to_pypy = "supportcode.generate_convert_to_pypy_vec(%s)" % (typ.convert_to_pypy, )

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
        self.convert_from_pypy = "supportcode.generate_convert_from_pypy_fvec(%s, %s)" % (number, typ.convert_from_pypy, )
        self.convert_to_pypy = "supportcode.generate_convert_to_pypy_fvec(%s, %s)" % (number, typ.convert_to_pypy, )

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
        self.argument_list = list(self.argtype.elements)
        self.restype = restype

    def __repr__(self):
        return "%s(%s, %r)" % (type(self).__name__, self.argtype, self.restype)

    def sail_repr(self):
        return "%s -> %s" % (self.argtype.sail_repr(), self.restype.sail_repr())


@unique
class Tuple(Type):
    def __init__(self, elements):
        self.elements = elements

    def __repr__(self):
        return "%s(%r)" % (type(self).__name__, self.elements)

    def sail_repr(self):
        return "(%s)" % (", ".join([el.sail_repr() for el in self.elements]))


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

class FixedBitVector(Type):
    pass # abstract base class

@unique
class SmallFixedBitVector(FixedBitVector):
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
class BigFixedBitVector(FixedBitVector):

    def __init__(self, width):
        # size known at compile time
        assert width > 64
        self.width = width
        self.uninitialized_value = "bitvector.SparseBitVector(%s, r_uint(0))" % width
        self.convert_to_pypy = "supportcode.generate_convert_to_pypy_big_fixed_bitvector(%s)" % width
        self.convert_from_pypy = "supportcode.generate_convert_from_pypy_big_fixed_bitvector(%s)" % width

    def sail_repr(self):
        return "bits(%s)" % (self.width, )

    def __repr__(self):
        return "BigFixedBitVector(%s)" % (self.width, )


@singleton
class GenericBitVector(Type):
    uninitialized_value = "bitvector.UNITIALIZED_BV"
    convert_to_pypy = "supportcode.convert_to_pypy_bitvector"
    convert_from_pypy = "supportcode.convert_from_pypy_bitvector"

    def sail_repr(self):
        return 'bits(?)'

    def __repr__(self):
        return "%s()" % (type(self).__name__, )

@singleton
class MachineInt(Type):
    uninitialized_value = "-0xfefe"
    convert_to_pypy = "supportcode.convert_to_pypy_machineint"
    convert_from_pypy = "supportcode.convert_from_pypy_machineint"


    def sail_repr(self):
        return 'int'

    def __repr__(self):
        return "%s()" % (type(self).__name__, )

@singleton
class Int(Type):
    uninitialized_value = "UninitInt"
    convert_to_pypy = "supportcode.convert_to_pypy_int"
    convert_from_pypy = "supportcode.convert_from_pypy_int"

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

@unique
class Packed(Type):
    def __init__(self, typ):
        self.uninitialized_value = typ.packed_field_pack(typ.uninitialized_value)
        self.typ = typ

    def __repr__(self):
        return "%s(%s)" % (type(self).__name__, self.typ)

