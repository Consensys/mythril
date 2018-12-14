"""This module declares classes to represent call data."""

from enum import Enum
from typing import Union, Any

from mythril.laser.smt import K, Array, If, simplify, Concat, Expression, BitVec

from mythril.laser.smt import symbol_factory
from mythril.laser.ethereum.util import get_concrete_int

from z3 import Model
from z3.z3types import Z3Exception


class CalldataType(Enum):
    CONCRETE = 1
    SYMBOLIC = 2


class BaseCalldata:
    """Base calldata class This represents the calldata provided when sending a
    transaction to a contract."""

    def __init__(self, tx_id):
        """

        :param tx_id:
        """
        self.tx_id = tx_id

    @property
    def calldatasize(self) -> Expression:
        """

        :return: Calldata size for this calldata object
        """
        result = self.size
        if isinstance(result, int):
            return symbol_factory.BitVecVal(result, 256)
        return result

    def get_word_at(self, offset: int) -> Expression:
        """Gets word at offset.

        :param offset:
        :return:
        """
        parts = self[offset : offset + 32]
        return simplify(Concat(parts))

    def __getitem__(self, item: Union[int, slice]) -> Any:
        """

        :param item:
        :return:
        """
        if isinstance(item, int) or isinstance(item, Expression):
            return self._load(item)

        if isinstance(item, slice):
            start = 0 if item.start is None else item.start
            step = 1 if item.step is None else item.step
            stop = self.size if item.stop is None else item.stop

            try:
                current_index = (
                    start
                    if isinstance(start, Expression)
                    else symbol_factory.BitVecVal(start, 256)
                )
                parts = []
                while simplify(current_index != stop):
                    element = self._load(current_index)
                    if not isinstance(element, Expression):
                        element = symbol_factory.BitVecVal(element, 8)

                    parts.append(element)
                    current_index = simplify(current_index + step)
            except Z3Exception:
                raise IndexError("Invalid Calldata Slice")

            return parts

        raise ValueError

    def _load(self, item: Union[int, Expression]) -> Any:
        """

        :param item:
        """
        raise NotImplementedError()

    @property
    def size(self) -> Union[Expression, int]:
        """Returns the exact size of this calldata, this is not normalized.

        :return: unnormalized call data size
        """
        raise NotImplementedError()

    def concrete(self, model: Model) -> list:
        """Returns a concrete version of the calldata using the provided model.

        :param model:
        """
        raise NotImplementedError


class ConcreteCalldata(BaseCalldata):
    """A concrete call data representation."""

    def __init__(self, tx_id: int, calldata: list):
        """Initializes the ConcreteCalldata object.

        :param tx_id: Id of the transaction that the calldata is for.
        :param calldata: The concrete calldata content
        """
        self._concrete_calldata = calldata
        self._calldata = K(256, 8, 0)
        for i, element in enumerate(calldata, 0):
            element = (
                symbol_factory.BitVecVal(element, 8)
                if isinstance(element, int)
                else element
            )
            self._calldata[symbol_factory.BitVecVal(i, 256)] = element

        super().__init__(tx_id)

    def _load(self, item: Union[int, Expression]) -> BitVec:
        """

        :param item:
        :return:
        """
        item = symbol_factory.BitVecVal(item, 256) if isinstance(item, int) else item
        return simplify(self._calldata[item])

    def concrete(self, model: Model) -> list:
        """

        :param model:
        :return:
        """
        return self._concrete_calldata

    @property
    def size(self) -> int:
        """

        :return:
        """
        return len(self._concrete_calldata)


class BasicConcreteCalldata(BaseCalldata):
    """A base class to represent concrete call data."""

    def __init__(self, tx_id: int, calldata: list):
        """Initializes the ConcreteCalldata object, that doesn't use z3 arrays.

        :param tx_id: Id of the transaction that the calldata is for.
        :param calldata: The concrete calldata content
        """
        self._calldata = calldata
        super().__init__(tx_id)

    def _load(self, item: Union[int, Expression]) -> Any:
        """

        :param item:
        :return:
        """
        if isinstance(item, int):
            try:
                return self._calldata[item]
            except IndexError:
                return 0

        value = symbol_factory.BitVecVal(0x0, 8)
        for i in range(self.size):
            value = If(item == i, self._calldata[i], value)
        return value

    def concrete(self, model: Model) -> list:
        """

        :param model:
        :return:
        """
        return self._calldata

    @property
    def size(self) -> int:
        """

        :return:
        """
        return len(self._calldata)


class SymbolicCalldata(BaseCalldata):
    """A class for representing symbolic call data."""

    def __init__(self, tx_id: int):
        """Initializes the SymbolicCalldata object.

        :param tx_id: Id of the transaction that the calldata is for.
        """
        self._size = symbol_factory.BitVecSym(str(tx_id) + "_calldatasize", 256)
        self._calldata = Array("{}_calldata".format(tx_id), 256, 8)
        super().__init__(tx_id)

    def _load(self, item: Union[int, Expression]) -> Any:
        """

        :param item:
        :return:
        """
        item = symbol_factory.BitVecVal(item, 256) if isinstance(item, int) else item
        return simplify(
            If(
                item < self._size,
                simplify(self._calldata[item]),
                symbol_factory.BitVecVal(0, 8),
            )
        )

    def concrete(self, model: Model) -> list:
        """

        :param model:
        :return:
        """
        concrete_length = model.eval(self.size.raw, model_completion=True).as_long()
        result = []
        for i in range(concrete_length):
            value = self._load(i)
            c_value = model.eval(value.raw, model_completion=True).as_long()
            result.append(c_value)

        return result

    @property
    def size(self) -> Expression:
        """

        :return:
        """
        return self._size


class BasicSymbolicCalldata(BaseCalldata):
    """A basic class representing symbolic call data."""

    def __init__(self, tx_id: int):
        """Initializes the SymbolicCalldata object.

        :param tx_id: Id of the transaction that the calldata is for.
        """
        self._reads = []
        self._size = BitVec(str(tx_id) + "_calldatasize", 256)
        super().__init__(tx_id)

    def _load(self, item: Union[int, Expression], clean=False) -> Any:
        x = symbol_factory.BitVecVal(item, 256) if isinstance(item, int) else item

        symbolic_base_value = If(
            x >= self._size,
            symbol_factory.BitVecVal(0, 8),
            BitVec("{}_calldata_{}".format(self.tx_id, str(item)), 8),
        )
        return_value = symbolic_base_value
        for r_index, r_value in self._reads:
            return_value = If(r_index == item, r_value, return_value)

        if not clean:
            self._reads.append((item, symbolic_base_value))
        return simplify(return_value)

    def concrete(self, model: Model) -> list:
        """

        :param model:
        :return:
        """
        concrete_length = get_concrete_int(model.eval(self.size, model_completion=True))
        result = []
        for i in range(concrete_length):
            value = self._load(i, clean=True)
            c_value = get_concrete_int(model.eval(value, model_completion=True))
            result.append(c_value)

        return result

    @property
    def size(self) -> Expression:
        """

        :return:
        """
        return self._size
