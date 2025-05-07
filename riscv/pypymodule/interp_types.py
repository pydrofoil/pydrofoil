from pypy.interpreter.error import oefmt
from pypy.interpreter.typedef import (TypeDef, interp2app, GetSetProperty,
    interp_attrproperty, interp_attrproperty_w)
from pypy.interpreter.gateway import unwrap_spec

from pydrofoil.mangle import demangle

from pydrofoil.types import *

class __extend__(Type):
    _attrs_ = []

def descr_type_new(space, w_cls):
    raise oefmt(space.w_TypeError, "can instantiate new sail types")

Type.typedef = TypeDef("_pydrofoil.sailtypes.SailType",
    __doc__ = """Instances of (subclasses of) this class represents a Sail
                 type. """,
    __new__ = interp2app(descr_type_new),
)
Type.typedef.acceptable_as_base_class = False

class __extend__(Union):
    def descr_get_constructors(self, space):
        res_w = [space.newtuple2(space.newtext(name), self.typs_list[index])
                     for index, name in enumerate(self.names_list)]
        return space.newlist(res_w)

Union.typedef = TypeDef("_pydrofoil.sailtypes.Union", Type.typedef,
    name = interp_attrproperty("demangled_name", Union, "the name of the union type", "newtext"),
    constructors = GetSetProperty(Union.descr_get_constructors),
)
Union.typedef.acceptable_as_base_class = False

class __extend__(Enum):
    def descr_get_elements(self, space):
        res_w = [space.newtext(element)
                    for element in self.elements_list]
        return space.newlist(res_w)

    def descr_repr(self, space):
        return space.newtext("<_pydrofoil.sailtypes.Enum %s { %s }>" % (self.demangled_name, " ".join(self.elements_list)))


Enum.typedef = TypeDef("_pydrofoil.sailtypes.Enum", Type.typedef,
    name = interp_attrproperty("demangled_name", Enum, "the name of the enum type", "newtext"),
    elements = GetSetProperty(Enum.descr_get_elements),
    __repr__ = interp2app(Enum.descr_repr),
)
Enum.typedef.acceptable_as_base_class = False

class __extend__(RegularStruct):
    def descr_get_fields(self, space):
        res_w = [space.newtuple2(space.newtext(name), self.typs_list[index])
                     for index, name in enumerate(self.names_list)]
        return space.newlist(res_w)
RegularStruct.typedef = TypeDef("_pydrofoil.sailtypes.Struct", Type.typedef,
    name = interp_attrproperty("demangled_name", RegularStruct, "the name of the struct type", "newtext"),
    fields = GetSetProperty(RegularStruct.descr_get_fields),
)
RegularStruct.typedef.acceptable_as_base_class = False

class __extend__(TupleStruct):
    def descr_len(self, space):
        return space.newint(len(self.typs_list))

    @unwrap_spec(index=int)
    def descr_getitem(self, space, index):
        if index < 0:
            index += len(self.typs_list)
        if not 0 <= index < len(self.typs_list):
            raise oefmt(space.w_IndexError, "index out of range")
        return self.typs_list[index]

TupleStruct.typedef = TypeDef("_pydrofoil.sailtypes.Tuple", Type.typedef,
    __len__ = interp2app(TupleStruct.descr_len),
    __getitem__ = interp2app(TupleStruct.descr_getitem),
)
TupleStruct.typedef.acceptable_as_base_class = False

class __extend__(Ref):
    pass
Ref.typedef = TypeDef("_pydrofoil.sailtypes.Ref", Type.typedef,
    of = interp_attrproperty_w("typ", Ref)
)
Ref.typedef.acceptable_as_base_class = False

class __extend__(Vec):
    pass
Vec.typedef = TypeDef("_pydrofoil.sailtypes.Vec", Type.typedef,
    of = interp_attrproperty_w("typ", Vec)
)
Vec.typedef.acceptable_as_base_class = False

class __extend__(FVec):
    pass
FVec.typedef = TypeDef("_pydrofoil.sailtypes.FVec", Type.typedef,
    of = interp_attrproperty_w("typ", FVec),
    length = interp_attrproperty("number", FVec, None, "newint"),
)
FVec.typedef.acceptable_as_base_class = False

class __extend__(Function):
    def descr_get_arguments(self, space):
        return space.newlist(self.argument_list[:])
    def descr_get_result(self, space):
        return self.restype
Function.typedef = TypeDef("_pydrofoil.sailtypes.Function", Type.typedef,
    arguments = GetSetProperty(Function.descr_get_arguments),
    result = GetSetProperty(Function.descr_get_result),
)
Function.typedef.acceptable_as_base_class = False

class __extend__(List):
    pass
List.typedef = TypeDef("_pydrofoil.sailtypes.List", Type.typedef,
)
List.typedef.acceptable_as_base_class = False

class __extend__(NullType):
    pass
NullType.typedef = TypeDef("_pydrofoil.sailtypes.Null", Type.typedef,
)
NullType.typedef.acceptable_as_base_class = False

@unwrap_spec(width="index")
def descr_bitvector_new(space, w_cls, width):
    if not 0 < width <= 64:
        raise oefmt(space.w_ValueError, "width must be between 1 and 64")
    return SmallFixedBitVector(width)

class __extend__(SmallFixedBitVector):
    def descr_repr(self, space):
        return space.newtext("_pydrofoil.sailtypes.SmallFixedBitVector(%s)" % (self.width, ))

SmallFixedBitVector.typedef = TypeDef("_pydrofoil.sailtypes.SmallFixedBitVector", Type.typedef,
    width = interp_attrproperty("width", SmallFixedBitVector, "the width of the bitvector", "newint"),
    __new__ = interp2app(descr_bitvector_new),
    __repr__ = interp2app(SmallFixedBitVector.descr_repr),
)
SmallFixedBitVector.typedef.acceptable_as_base_class = False

@unwrap_spec(width="index")
def descr_big_bitvector_new(space, w_cls, width):
    if width <= 64:
        raise oefmt(space.w_ValueError, "width must be larger than 64")
    return BigFixedBitVector(width)

class __extend__(BigFixedBitVector):
    def descr_repr(self, space):
        return space.newtext("_pydrofoil.sailtypes.BigFixedBitVector(%s)" % (self.width, ))
BigFixedBitVector.typedef = TypeDef("_pydrofoil.sailtypes.BigFixedBitVector", Type.typedef,
    width = interp_attrproperty("width", BigFixedBitVector, "the width of the bitvector", "newint"),
    __new__ = interp2app(descr_big_bitvector_new),
    __repr__ = interp2app(BigFixedBitVector.descr_repr),
)
BigFixedBitVector.typedef.acceptable_as_base_class = False

class __extend__(GenericBitVector):
    pass
GenericBitVector.typedef = TypeDef("_pydrofoil.sailtypes.GenericBitVector", Type.typedef,
)
GenericBitVector.typedef.acceptable_as_base_class = False

class __extend__(MachineInt):
    pass

MACHINEINT = MachineInt()

def descr_machineint_new(space, w_cls):
    return MACHINEINT

MachineInt.typedef = TypeDef("_pydrofoil.sailtypes.MachineInt", Type.typedef,
    __new__ = interp2app(descr_machineint_new),
)
MachineInt.typedef.acceptable_as_base_class = False


class __extend__(Int):
    pass

INT = Int()

def descr_int_new(space, w_cls):
    return INT

Int.typedef = TypeDef("_pydrofoil.sailtypes.Int", Type.typedef,
    __new__ = interp2app(descr_int_new),
)
Int.typedef.acceptable_as_base_class = False

class __extend__(Bool):
    pass

BOOL = Bool()

def descr_bool_new(space, w_cls):
    return BOOL

Bool.typedef = TypeDef("_pydrofoil.sailtypes.Bool", Type.typedef,
    __new__ = interp2app(descr_bool_new),
)
Bool.typedef.acceptable_as_base_class = False

class __extend__(Unit):
    pass

UNIT = Unit()

def descr_unit_new(space, w_cls):
    return UNIT

Unit.typedef = TypeDef("_pydrofoil.sailtypes.Unit", Type.typedef,
    __new__ = interp2app(descr_unit_new),
)
Unit.typedef.acceptable_as_base_class = False

class __extend__(String):
    pass

STRING = String()

def descr_string_new(space, w_cls):
    return STRING

String.typedef = TypeDef("_pydrofoil.sailtypes.String", Type.typedef,
    __new__ = interp2app(descr_string_new),
)
String.typedef.acceptable_as_base_class = False


class __extend__(Real):
    pass

REAL = Real()

def descr_real_new(space, w_cls):
    return REAL

Real.typedef = TypeDef("_pydrofoil.sailtypes.Real", Type.typedef,
    __new__ = interp2app(descr_real_new),
)

Real.typedef.acceptable_as_base_class = False

