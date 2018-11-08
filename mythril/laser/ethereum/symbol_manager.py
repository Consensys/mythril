from z3 import BitVec, BitVecRef, is_bv


class Symbol:
    """Each symbol in Mythril is composed of the the underlying raw symbol
    object `_raw` created by Z3 API and the additional properties `_props`
    of this symbol. Properties are managed by Mythril and do not affect the
    constraint solvers.

    """

    __slots__ = ["_raw", "_props"]

    def __init__(self, raw):
        self._raw = raw
        self._props = dict()

    def get_raw(self):
        """Get the raw symbol object created by Z3.

        :return: the raw symbol object created by Z3

        """
        return self._raw

    def set_prop(self, name: str, value):
        """Set the property `name` to `value`.

        :param name: the name of the property
        :param value: the value of the property

        """
        self._props[name] = value

    def get_prop(self, name: str):
        """Get the value of a set property `name`.

        :param name: the name of the property

        :return: the value of the property `name` if it has been set

        :raise KeyError: if the property `name` has not been set for this symbol

        """
        return self._props[name]


class SymRedefError(Exception):
    """Raise if attempting to recreate an existing symbol with different
    type.

    """

    def __init__(self, name: str):
        self.name = name

    def __str__(self):
        return "symbol `{}` redefined".format(self.name)


class SymFactory:
    """A singleton symbol factory. All symbols used in Mythril should be
    created from the symbol factory, in order to ease the lookup of
    symbols by names.

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
        """Reset the symbol factor, which discards all previously created
        symbols.

        """
        self._symbols = dict()

    def get_bv_symbol(self, name: str, width: int) -> Symbol:
        """Get a bit vector symbol of the specified name and width. If a bit
        vector symbol of the same name and width has been created, then just
        return that symbol. If a symbol of the same name is not a bit vector,
        or has a different width, then an exception SymRedefError will be
        raised.

        :param name: the name of the symbol
        :param width: the bit width of the symbol

        :return: a new symbol if no symbol of the name `name` and width `width`
                 has been created; or the existing symbol if one has been created.

        :raise SymRedefError: if a symbol of name `name` has been created and is
                              not a bit vector or has a different width

        """

        if name in self._symbols.keys():
            sym = self._symbols[name]
            raw = sym.get_raw()

            if (not is_bv(raw)) or raw.size() != width:
                raise SymRedefError(name)

            return sym

        sym = Symbol(BitVec(name, width))
        self._symbols[name] = sym

        return sym

    def lookup_symbol(self, name: str) -> Symbol:
        """Get the existing symbol of name `name`.

        :param name: the name of the symbol

        :return: the symbol if existing

        :raise KeyError: if the symbol `name` has not been created

        """
        return self._symbols[name]


sym_factory = SymFactory()


def sym_get_bv(name: str, width: int) -> BitVecRef:
    """Get a bit vector symbol of the specified name and width. If a bit
    vector symbol of the same name and width has been created, then
    just return that symbol. If a symbol of the same name is not a bit
    vector, or has a different width, then an exception SymRedefError
    will be raised.

    :param name: the name of the symbol
    :param width: the bit width of the symbol

    :return: a new symbol if no symbol of the name `name` and width `width`
             has been created; or the existing symbol if one has been created.

    :raise SymRedefError: if a symbol of name `name` has been created and is
                          not a bit vector or has a different width

    """
    return sym_factory.get_bv_symbol(name, width).get_raw()


def sym_get_prop(sym_name: str, prop_name: str):
    """Get the value of a set symbol property `prop_name`.

    :param sym_name: the name of the symbol
    :param prop_name: the name of the property

    :return: the value of the property `prop_name` if it has been set

    :raise KeyError: if the property `prop_name` has not been set for this symbol

    """

    sym = sym_factory.lookup_symbol(sym_name)
    return sym.get_prop(prop_name)


def sym_set_prop(sym_name: str, prop_name: str, prop_value):
    """Set the symbol property `prop_name` to `prop_value`.

    :param sym_name: the name of the symbol
    :param prop_name: the name of the property
    :param prop_value: the value of the property

    """

    sym = sym_factory.lookup_symbol(sym_name)
    sym.set_prop(prop_name, prop_value)
