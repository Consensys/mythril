"""This module declares classes to represent creation code and call data."""
from typing import cast, Union, Tuple, List


from enum import Enum
from typing import Any, Union

from z3 import Model
from z3.z3types import Z3Exception

from mythril.laser.ethereum.util import get_concrete_int
from mythril.laser.smt import (
    Array,
    BitVec,
    Bool,
    Concat,
    Expression,
    If,
    K,
    simplify,
    symbol_factory,
)

from mythril.laser.smt.bitvec_helper import Sum

from mythril.laser.ethereum.state.calldata import BaseCalldata


class CreationData:
    """CreationData class This represents creation bytecode and calldata constructor argument provided when sending a
    transaction to a contract."""

    def __init__(self, code, calldata: BaseCalldata) -> None:
        """

        :param tx_id:
        """
        self.code = code
        self.calldata = calldata

    @property
    def size(self) -> BitVec:
        """

        :return: codesize in bytes for this CreationData object
        """
        calldata_size = self.calldata.calldatasize
        code_size = symbol_factory.BitVecVal(len(self.code) // 2, 256)
        if calldata_size.symbolic:
            return Sum(code_size, calldata_size)
        return code_size + calldata_size
