from enum import Enum
from typing import Union, Any
from z3 import (
    BitVecVal,
    BitVecRef,
    BitVecSort,
    BitVec,
    Implies,
    simplify,
    Concat,
    UGT,
    Array,
)
from z3.z3types import Z3Exception

from mythril.laser.ethereum.util import get_concrete_int


class CalldataType(Enum):
    CONCRETE = 1
    SYMBOLIC = 2


class Calldata:
    """
    Calldata class representing the calldata of a transaction
    """

    def __init__(self, tx_id, starting_calldata=None):
        """
        Constructor for Calldata
        :param tx_id: unique value representing the transaction the calldata is for
        :param starting_calldata: byte array representing the concrete calldata of a transaction
        """
        self.tx_id = tx_id
        if starting_calldata is not None:
            self._calldata = []
            self.calldatasize = BitVecVal(len(starting_calldata), 256)
            self.concrete = True
        else:
            self._calldata = Array(
                "{}_calldata".format(self.tx_id), BitVecSort(256), BitVecSort(8)
            )
            self.calldatasize = BitVec("{}_calldatasize".format(self.tx_id), 256)
            self.concrete = False

        if self.concrete:
            for calldata_byte in starting_calldata:
                if type(calldata_byte) == int:
                    self._calldata.append(BitVecVal(calldata_byte, 8))
                else:
                    self._calldata.append(calldata_byte)

    def concretized(self, model):
        result = []
        for i in range(
            get_concrete_int(model.eval(self.calldatasize, model_completion=True))
        ):
            result.append(
                get_concrete_int(model.eval(self._calldata[i], model_completion=True))
            )

        return result

    def get_word_at(self, index: int):
        return self[index : index + 32]

    def __getitem__(self, item: Union[int, slice]) -> Any:
        if isinstance(item, slice):
            start, step, stop = item.start, item.step, item.stop
            try:
                if start is None:
                    start = 0
                if step is None:
                    step = 1
                if stop is None:
                    stop = self.calldatasize
                current_index = (
                    start if isinstance(start, BitVecRef) else BitVecVal(start, 256)
                )
                dataparts = []
                while simplify(current_index != stop):
                    dataparts.append(self[current_index])
                    current_index = simplify(current_index + step)
            except Z3Exception:
                raise IndexError("Invalid Calldata Slice")

            values, constraints = zip(*dataparts)
            result_constraints = []
            for c in constraints:
                result_constraints.extend(c)
            return simplify(Concat(values)), result_constraints

        if self.concrete:
            try:
                return self._calldata[get_concrete_int(item)], ()
            except IndexError:
                return BitVecVal(0, 8), ()
        else:
            constraints = [
                Implies(self._calldata[item] != 0, UGT(self.calldatasize, item))
            ]

            return self._calldata[item], constraints
