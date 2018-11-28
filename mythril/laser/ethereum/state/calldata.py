from enum import Enum
from typing import Union, Any
from z3 import BitVecVal, BitVecRef, BitVec, simplify, Concat, If, ExprRef
from z3.z3types import Z3Exception, Model

from mythril.laser.ethereum.util import get_concrete_int


class CalldataType(Enum):
    CONCRETE = 1
    SYMBOLIC = 2


class BaseCalldata:
    """
    Base calldata class
    This represents the calldata provided when sending a transaction to a contract
    """
    def __init__(self, tx_id):
        self.tx_id = tx_id

    @property
    def calldatasize(self) -> ExprRef:
        """
        :return: Calldata size for this calldata object
        """
        result = self.size
        if isinstance(result, int):
            return BitVecVal(result, 256)
        return result

    def get_word_at(self, offset: int) -> ExprRef:
        """ Gets word at offset"""
        return self[offset: offset + 32]

    def __getitem__(self, item: Union[int, slice]) -> Any:
        if isinstance(item, int) or isinstance(item, ExprRef):
            return self._load(item)

        if isinstance(item, slice):
            start = 0 if item.start is None else item.start
            step = 1 if item.step is None else item.step
            stop = self.size if item.stop is None else item.stop

            try:
                current_index = (
                    start if isinstance(start, BitVecRef) else BitVecVal(start, 256)
                )
                parts = []
                while simplify(current_index != stop):
                    parts.append(self._load(current_index))
                    current_index = simplify(current_index + step)
            except Z3Exception:
                raise IndexError("Invalid Calldata Slice")

            return simplify(Concat(parts))

        raise ValueError

    def _load(self, item: Union[int, ExprRef]) -> Any:
        raise NotImplementedError()

    @property
    def size(self) -> Union[ExprRef, int]:
        """ Returns the exact size of this calldata, this is not normalized"""
        raise NotImplementedError()

    def concrete(self, model: Model) -> list:
        """ Returns a concrete version of the calldata using the provided model"""
        raise NotImplementedError


class ConcreteCalldata(BaseCalldata):
    def __init__(self, tx_id: int, calldata: list):
        """
        Initializes the ConcreteCalldata object
        :param tx_id: Id of the transaction that the calldata is for.
        :param calldata: The concrete calldata content
        """
        self._calldata = calldata
        super().__init__(tx_id)

    def _load(self, item: Union[int, ExprRef]) -> Any:
        if isinstance(item, int):
            try:
                return self._calldata[item]
            except IndexError:
                return 0

        value = BitVecVal(0x0, 8)
        for i in range(self.size):
            value = If(item == i, self._calldata[i], value)
        return value

    def concrete(self, model: Model) -> list:
        return self._calldata

    @property
    def size(self) -> int:
        return len(self._calldata)


class SymbolicCalldata(BaseCalldata):
    def __init__(self, tx_id: int):
        """
        Initializes the SymbolicCalldata object
        :param tx_id: Id of the transaction that the calldata is for.
        """
        self._reads = []
        self._size = BitVec("calldatasize", 256)
        super().__init__(tx_id)

    def _load(self, item: Union[int, ExprRef], clean=False) -> Any:
        x = BitVecVal(item, 256) if isinstance(item, int) else item

        symbolic_base_value = If(
            x > self._size,
            BitVecVal(0, 8),
            BitVec("{}_calldata_{}".format(self.tx_id, str(item)), 8)
        )

        return_value = symbolic_base_value
        for r_index, r_value in self._reads:
            return_value = If(r_index == item, r_value, return_value)

        if not clean:
            self._reads.append((item, symbolic_base_value))
        return simplify(return_value)

    def concrete(self, model: Model) -> list:
        concrete_length = get_concrete_int(model.eval(self.size, model_completion=True))
        result = []
        for i in range(concrete_length):
            value = self._load(i, clean=True)
            c_value = get_concrete_int(model.eval(value, model_completion=True))
            result.append(c_value)

        return result

    @property
    def size(self) -> ExprRef:
        return self._size
