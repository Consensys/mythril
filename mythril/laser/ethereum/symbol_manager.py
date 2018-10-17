from pysmt.shortcuts import Symbol, reset_env, get_env
from pysmt.fnode import FNode
from pysmt.typing import PySMTType


class Sym:
    """
    Each symbol in Mythril is composed of the the underlying raw symbol object
    `_raw` created by pySMT and the additional properties `_props` of this
    symbol. Properties are managed by Mythril and do not affect the constraint
    solvers.
    """

    __slots__ = ["_raw", "_props"]

    def __init__(self, raw: FNode):
        self._raw = raw
        self._props = dict()

    def get_raw(self) -> FNode:
        """
        Get the raw symbol object created by pySMT.

        :return: the raw symbol object created by pySMT
        """
        return self._raw

    def set_prop(self, name: str, value):
        """
        Set the property `name` to `value`.

        :param name: the name of the property
        :param value: the value of the property
        """
        self._props[name] = value

    def get_prop(self, name: str):
        """
        Get the value of a set property `name`.

        :param name: the name of the property

        :return: the value of the property `name` if it has been set

        :raise KeyError: if the property `name` has not been set for this symbol
        """
        return self._props[name]


class SymFactory:
    """
    A singleton symbol factory. All symbols used in Mythril should be created
    from the symbol factory, in order to ease the lookup of symbols by names.
    """

    __slots__ = ["_symbols"]
    __instance = None

    def __init__(self):
        self.reset()

    def __new__(cls):
        if SymFactory.__instance is None:
            SymFactory.__instance = object.__new__(cls)
        return SymFactory.__instance

    def reset(self):
        """
        Reset the symbol factor, which discards all previously created symbols.
        """
        reset_env()
        get_env().enable_infix_notation = True
        self._symbols = dict()

    def get_symbol(self, name: str, typ: PySMTType) -> Sym:
        """
        Create a new symbol or get the existing symbol of the specified
        `name` and type `typ`.

        :param name: the name of the symbol
        :param typ: the type of the symbol, which is in the type PySMTType,
                    e.g., pySMT.typing.INT, pySMT.typing.BVType(256), etc.

        :return: a new symbol if no symbol of the name `name` and type `typ` has
                 been created ever; or the existing symbol if it has been created.

        :raise SymRedefError: if a symbol of name `name` has been created and is
                              in the different type than `typ`.
        """

        if name in self._symbols.keys():
            if self._symbols[name].get_raw().get_type() != typ:
                raise SymRedefError(name)
            return self._symbols[name]

        sym = Sym(Symbol(name, typ))
        self._symbols[name] = sym

        return sym

    def lookup_symbol(self, name: str) -> Sym:
        """
        Get the existing symbol of name `name`.

        :param name: the name of the symbol

        :return: the symbol if existing

        :raise KeyError: if the symbol `name` has not been created
        """
        return self._symbols[name]


class SymRedefError(Exception):
    """
    Raise if attempting to recreate an existing symbol with different type.
    """

    def __init__(self, name: str):
        self.name = name

    def __str__(self):
        return "symbol `{}` redefined".format(self.name)


factory = SymFactory()


def sym_get(name: str, typ) -> Sym:
    """
    Create a new symbol or get the existing symbol of the specified `name` and
    type `typ`.

    :param name: the name of the symbol
    :param typ: the type of the symbol, which is in the type PySMTType,
                e.g., pySMT.typing.INT, pySMT.typing.BVType(256), etc.

    :return: a new symbol if no symbol of the name `name` and type `typ` has
             been created ever; or the existing symbol if it has been created.

    :raise SymRedefError: if a symbol of name `name` has been created and is
                          in the different type than `typ`.
    """
    return factory.get_symbol(name, typ)


def sym_get_prop(sym_name: str, prop_name: str):
    """
    Get the value of a set symbol property `prop_name`.

    :param sym_name: the name of the symbol
    :param prop_name: the name of the property

    :return: the value of the property `prop_name` if it has been set

    :raise KeyError: if the property `prop_name` has not been set for this symbol
    """

    sym = factory.lookup_symbol(sym_name)
    return sym.get_prop(prop_name)


def sym_set_prop(sym_name: str, prop_name: str, prop_value):
    """
    Set the symbol property `prop_name` to `prop_value`.

    :param sym_name: the name of the symbol
    :param prop_name: the name of the property
    :param prop_value: the value of the property
    """

    sym = factory.lookup_symbol(sym_name)
    sym.set_prop(prop_name, prop_value)
