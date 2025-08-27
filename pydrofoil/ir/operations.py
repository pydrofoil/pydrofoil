from typing import cast
from pydrofoil import types, bitvector
from rpython.rlib.rarithmetic import r_uint


class Value(object):
    def __init__(self, resolved_type):
        # type: (types.Type) -> None
        self.resolved_type = resolved_type

    def is_union_creation(self):
        return False

    def _repr(self, print_varnames):
        return repr(self)

    def _get_print_name(self, print_varnames):
        if self in print_varnames:
            name = print_varnames[self]
        else:
            name = "i%s" % (len(print_varnames),)
            print_varnames[self] = name
        return name

    def getargs(self):
        return []

    def comparison_key(self):
        return self

    def __repr__(self):
        return "<%s %x>" % (self.__class__.__name__, id(self))


class Argument(Value):
    def __init__(self, name, resolved_type):
        super(Argument, self).__init__(resolved_type)
        self.name = name

    def __repr__(self):
        return "Argument(%r, %r)" % (self.name, self.resolved_type)

    def _repr(self, print_varnames):
        return self.name


class Operation(Value):
    can_have_side_effects = True

    def __init__(
        self, name, args, resolved_type, sourcepos=None, varname_hint=None
    ):
        for arg in args:
            assert isinstance(arg, Value)
        self.name = name
        self.args = args  # type: list[Value]
        self.resolved_type = resolved_type
        assert isinstance(sourcepos, (str, type(None)))
        self.sourcepos = sourcepos
        self.varname_hint = varname_hint

    def __repr__(self):
        return "%s(%r, %r, %r, %r)" % (
            self.__class__.__name__,
            self.name,
            self.args,
            self.resolved_type,
            self.sourcepos,
        )

    def _repr(self, print_varnames):
        return self._get_print_name(print_varnames)

    def getargs(self):
        return self.args

    def replace_ops(self, replacements):
        assert self not in replacements
        res = False
        for index, arg in enumerate(self.args):
            if arg in replacements:
                self.args[index] = replacements[arg]
                res = True
        return res

    def is_union_creation(self):
        return (
            isinstance(self.resolved_type, types.Union)
            and type(self) is Operation
            and self.name in self.resolved_type.variants
        )


class Cast(Operation):
    can_have_side_effects = False

    def __init__(self, arg, resolved_type, sourcepos=None, varname_hint=None):
        Operation.__init__(
            self, "$cast", [arg], resolved_type, sourcepos, varname_hint
        )

    def __repr__(self):
        return "Cast(%r, %r, %r)" % (
            self.args[0],
            self.resolved_type,
            self.sourcepos,
        )


class Allocate(Operation):
    can_have_side_effects = False

    def __init__(self, resolved_type, sourcepos):
        Operation.__init__(self, "$allocate", [], resolved_type, sourcepos)

    def __repr__(self):
        return "Allocate(%r, %r)" % (
            self.resolved_type,
            self.sourcepos,
        )


class StructConstruction(Operation):
    can_have_side_effects = False

    def __repr__(self):
        return "StructConstruction(%r, %r, %r)" % (
            self.name,
            self.args,
            self.resolved_type,
        )


class StructCopy(Operation):
    can_have_side_effects = False

    def __init__(self, name, arg, resolved_type, sourcepos=None):
        Operation.__init__(self, name, [arg], resolved_type, sourcepos)

    def __repr__(self):
        return "StructCopy(%r, %r, %r, %r)" % (
            self.name,
            self.args[0],
            self.resolved_type,
            self.sourcepos,
        )


class FieldAccess(Operation):
    can_have_side_effects = False

    def __repr__(self):
        return "%s(%r, %r, %r)" % (
            self.__class__.__name__,
            self.name,
            self.args,
            self.resolved_type,
        )


class FieldWrite(Operation):
    def __init__(
        self, name, args, resolved_type=None, sourcepos=None, varname_hint=None
    ):
        if resolved_type is None:
            resolved_type = types.Unit()
        Operation.__init__(
            self, name, args, resolved_type, sourcepos, varname_hint
        )

    def __repr__(self):
        return "%s(%r, %r)" % (self.__class__.__name__, self.name, self.args)


class UnionVariantCheck(Operation):
    can_have_side_effects = False

    def __repr__(self):
        return "UnionVariantCheck(%r, %r, %r)" % (
            self.name,
            self.args,
            self.resolved_type,
        )


class UnionCast(Operation):
    can_have_side_effects = False

    def __repr__(self):
        return "UnionCast(%r, %r, %r)" % (
            self.name,
            self.args,
            self.resolved_type,
        )


class GlobalRead(Operation):
    can_have_side_effects = False

    def __init__(self, name, resolved_type):
        Operation.__init__(self, name, [], resolved_type, None)

    def __repr__(self):
        return "GlobalRead(%r, %r)" % (self.name, self.resolved_type)


class GlobalWrite(Operation):
    def __repr__(self):
        return "GlobalWrite(%r, %r, %r)" % (
            self.name,
            self.args,
            self.resolved_type,
        )


class RefAssignment(Operation):
    def __init__(self, args, resolved_type, sourcepos):
        Operation.__init__(self, "$ref-assign", args, resolved_type, sourcepos)

    def __repr__(self):
        return "RefAssignment(%r, %r, %r)" % (
            self.args,
            self.resolved_type,
            self.sourcepos,
        )


class RefOf(Operation):
    can_have_side_effects = False

    def __init__(self, name, resolved_type, sourcepos=None):
        Operation.__init__(self, name, [], resolved_type, sourcepos)

    def __repr__(self):
        return "RefOf(%r, %r, %r)" % (
            self.name,
            self.resolved_type,
            self.sourcepos,
        )


class VectorInit(Operation):
    can_have_side_effects = False

    def __init__(self, size, resolved_type, sourcepos):
        Operation.__init__(
            self, "$zinternal_vector_init", [size], resolved_type, sourcepos
        )

    def __repr__(self):
        return "VectorInit(%r, %r, %r)" % (
            self.args[0],
            self.resolved_type,
            self.sourcepos,
        )


class VectorUpdate(Operation):
    can_have_side_effects = False

    def __init__(self, args, resolved_type, sourcepos):
        Operation.__init__(
            self, "$zinternal_vector_update", args, resolved_type, sourcepos
        )

    def __repr__(self):
        return "VectorUpdate(%r, %r, %r)" % (
            self.args,
            self.resolved_type,
            self.sourcepos,
        )


class NonSSAAssignment(Operation):
    def __init__(self, lhs, rhs):
        Operation.__init__(
            self, "non_ssa_assign", [lhs, rhs], types.Unit(), None
        )

    def __repr__(self):
        return "NonSSAAssignment(%r, %r)" % (self.args[0], self.args[1])


class Comment(Operation):
    def __init__(self, comment):
        Operation.__init__(self, comment, [], types.Unit())


class UnpackPackedField(Operation):
    can_have_side_effects = False

    def __init__(self, arg, sourcepos=None):
        assert isinstance(arg.resolved_type, types.Packed)
        Operation.__init__(
            self, "$unpack", [arg], arg.resolved_type.typ, sourcepos
        )

    def __repr__(self):
        return "UnpackPackedField(%s)" % self.args[0]


class PackPackedField(Operation):
    can_have_side_effects = False

    def __init__(self, arg, sourcepos=None):
        assert isinstance(
            arg.resolved_type,
            (types.Int, types.GenericBitVector, types.BigFixedBitVector),
        )
        Operation.__init__(
            self, "$pack", [arg], types.Packed(arg.resolved_type), sourcepos
        )

    def __repr__(self):
        return "PackPackedField(%s)" % self.args[0]


class Phi(Value):
    can_have_side_effects = False

    def __init__(self, prevblocks, prevvalues, resolved_type):
        from pydrofoil.ir import Block

        for block in prevblocks:
            assert isinstance(block, Block)
        for value in prevvalues:
            assert isinstance(value, Value) or value is None
        self.prevblocks = prevblocks
        self.prevvalues = prevvalues
        self.resolved_type = resolved_type

    def _repr(self, print_varnames):
        return self._get_print_name(print_varnames)

    def getargs(self):
        return self.prevvalues

    def replace_ops(self, replacements):
        assert self not in replacements
        res = False
        for index, op in enumerate(self.prevvalues):
            if op in replacements:
                self.prevvalues[index] = replacements[op]
                res = True
        return res


class Constant(Value):
    pass


class BooleanConstant(Constant):
    TRUE = cast("BooleanConstant", None)
    FALSE = cast("BooleanConstant", None)

    def __init__(self, value):
        assert isinstance(value, bool)
        self.value = value
        self.resolved_type = types.Bool()

    def _repr(self, print_varnames):
        if self.value:
            return "BooleanConstant.TRUE"
        else:
            return "BooleanConstant.FALSE"

    def __repr__(self):
        return self._repr({})

    @staticmethod
    def frombool(value):
        return BooleanConstant.TRUE if value else BooleanConstant.FALSE


BooleanConstant.TRUE = BooleanConstant(True)
BooleanConstant.FALSE = BooleanConstant(False)


class MachineIntConstant(Constant):
    resolved_type = types.MachineInt()

    def __init__(self, number):
        assert isinstance(number, int)
        self.number = number

    def _repr(self, print_varnames):
        return repr(self)

    def comparison_key(self):
        return (MachineIntConstant, self.number, self.resolved_type)

    def __repr__(self):
        return "MachineIntConstant(%r)" % (self.number,)


class IntConstant(Constant):
    resolved_type = types.Int()

    def __init__(self, number):
        # type: (int) -> None
        self.number = number

    def _repr(self, print_varnames):
        return repr(self)

    def comparison_key(self):
        return (IntConstant, self.number, self.resolved_type)

    def __repr__(self):
        return "IntConstant(%r)" % (self.number,)


class SmallBitVectorConstant(Constant):
    def __init__(self, value, resolved_type):
        if isinstance(value, int):
            value = r_uint(value)
        assert isinstance(value, r_uint)
        assert isinstance(resolved_type, types.SmallFixedBitVector)
        self.value = value
        self.resolved_type = resolved_type

    @staticmethod
    def from_ruint(size, val):
        return SmallBitVectorConstant(val, types.SmallFixedBitVector(size))

    def comparison_key(self):
        return (SmallBitVectorConstant, self.value, self.resolved_type)

    def _repr(self, print_varnames):
        return repr(self)

    def __repr__(self):
        size = self.resolved_type.width
        val = self.value
        if size % 4 == 0:
            value = hex(int(val))
        else:
            value = bin(int(val))
        return "SmallBitVectorConstant(%s, %s)" % (value, self.resolved_type)


class GenericBitVectorConstant(Constant):
    resolved_type = types.GenericBitVector()

    def __init__(self, value):
        assert isinstance(value, bitvector.BitVector)
        self.value = value

    def comparison_key(self):
        return (
            GenericBitVectorConstant,
            self._construction_expr(),
            self.resolved_type,
        )

    def _repr(self, print_varnames):
        return repr(self)

    def _construction_expr(self):
        val = self.value.tolong()
        size = self.value.size()
        if size % 4 == 0:
            value = hex(int(val))
        else:
            value = bin(int(val))
        if isinstance(
            self.value, (bitvector.SparseBitVector, bitvector.SmallBitVector)
        ):
            return "bitvector.from_ruint(%s, r_uint(%s))" % (
                size,
                self.value.val,
            )
        return "bitvector.from_bigint(%s, rbigint.fromlong(%s))" % (
            size,
            value,
        )

    def __repr__(self):
        return "GenericBitVectorConstant(%s)" % self._construction_expr()


class DefaultValue(Constant):
    def __init__(self, resolved_type):
        self.resolved_type = resolved_type

    def comparison_key(self):
        return (DefaultValue, self.resolved_type)

    def __repr__(self):
        return "DefaultValue(%r)" % (self.resolved_type,)


class EnumConstant(Constant):
    def __init__(self, variant, resolved_type):
        self.variant = variant
        self.resolved_type = resolved_type

    def comparison_key(self):
        return (EnumConstant, self.variant, self.resolved_type)

    def __repr__(self):
        return "EnumConstant(%r, %r)" % (self.variant, self.resolved_type)


class StringConstant(Constant):
    resolved_type = types.String()

    def __init__(self, string):
        self.string = string

    def comparison_key(self):
        return (StringConstant, self.string, self.resolved_type)

    def __repr__(self):
        return "StringConstant(%r)" % (self.string,)


class UnitConstant(Constant):
    resolved_type = types.Unit()

    UNIT = cast("UnitConstant", None)

    def __repr__(self):
        return "UnitConstant.UNIT"


UnitConstant.UNIT = UnitConstant(types.Unit())

# next


class Next(object):
    def __init__(self, sourcepos):
        self.sourcepos = sourcepos

    def next_blocks(self):
        return []

    def getargs(self):
        return []

    def replace_next(self, block, otherblock):
        pass

    def replace_ops(self, replacements):
        return False

    def _repr(self, print_varnames):
        return self.__class__.__name__


class Return(Next):
    def __init__(self, value, sourcepos=None):
        assert isinstance(value, Value) or value is None
        self.value = value  # type: Value
        self.sourcepos = sourcepos

    def getargs(self):
        return [self.value] if self.value is not None else []

    def replace_ops(self, replacements):
        if self.value in replacements:
            self.value = replacements[self.value]
            return True
        return False

    def _repr(self, print_varnames, blocknames=None):
        return "Return(%s, %r)" % (
            None if self.value is None else self.value._repr(print_varnames),
            self.sourcepos,
        )


class Raise(Next):
    def __init__(self, kind, sourcepos=None):
        self.kind = kind
        self.sourcepos = sourcepos

    def getargs(self):
        return [self.kind]

    def replace_ops(self, replacements):
        if self.kind in replacements:
            self.kind = replacements[self.kind]
            return True
        return False

    def _repr(self, print_varnames, blocknames=None):
        return "Raise(%s, %r)" % (self.kind, self.sourcepos)


class JustStop(Next):
    def __init__(self):
        self.sourcepos = None

    def _repr(self, print_varnames, blocknames=None):
        return "JustStop(%r)" % (self.sourcepos,)


class Goto(Next):
    def __init__(self, target, sourcepos=None):
        from pydrofoil.ir import Block

        assert isinstance(target, Block)
        self.target = target
        self.sourcepos = sourcepos

    def next_blocks(self):
        return [self.target]

    def replace_next(self, block, otherblock):
        if self.target is block:
            self.target = otherblock

    def _repr(self, print_varnames, blocknames=None):
        if blocknames:
            return "Goto(%s, %r)" % (blocknames[self.target], self.sourcepos)
        return "goto"


class ConditionalGoto(Next):
    def __init__(self, booleanvalue, truetarget, falsetarget, sourcepos=None):
        from pydrofoil.ir import Block

        assert isinstance(truetarget, Block)
        assert isinstance(falsetarget, Block)
        assert isinstance(booleanvalue, Value)
        self.truetarget = truetarget
        self.falsetarget = falsetarget
        self.booleanvalue = booleanvalue
        self.sourcepos = sourcepos

    def getargs(self):
        return [self.booleanvalue]

    def next_blocks(self):
        return [self.falsetarget, self.truetarget]

    def replace_next(self, block, otherblock):
        if self.truetarget is block:
            self.truetarget = otherblock
        if self.falsetarget is block:
            self.falsetarget = otherblock

    def replace_ops(self, replacements):
        if self.booleanvalue in replacements:
            self.booleanvalue = replacements[self.booleanvalue]
            return True
        return False

    def _repr(self, print_varnames, blocknames=None):
        if blocknames:
            return "ConditionalGoto(%s, %s, %s, %r)" % (
                self.booleanvalue._repr(print_varnames),
                blocknames[self.truetarget],
                blocknames[self.falsetarget],
                self.sourcepos,
            )
        return "goto if %s" % (self.booleanvalue._repr(print_varnames),)


class RangeCheck(Operation):
    """
    Result of a range analysis on some value.

    May be used by other analyses.

    Parameters
    ----------
    value: Value | Return
        The value that this range refers to.
    low: int | None
        The lower bound of the value.
    high: int | None
        The upper bound of the value.
    message: str, optional
        A message to display in the generated assert-statement.
    """

    def __init__(self, value, low, high, message=""):
        # type: (Value | Return, int | None, int | None, str) -> None
        super(RangeCheck, self).__init__(
            "$rangecheck",
            [
                value,
                UnitConstant.UNIT if low is None else IntConstant(low),
                UnitConstant.UNIT if high is None else IntConstant(high),
                StringConstant(message),
            ],
            types.Unit(),
        )
