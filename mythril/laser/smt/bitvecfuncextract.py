import z3

from typing import Optional, List
from mythril.laser.smt.bitvecfunc import BitVecFunc
from mythril.laser.smt.bitvec import Annotations, BitVec


class BitVecFuncExtract(BitVecFunc):
    """A bit vector function wrapper, useful for preserving Extract() and Concat() operations"""

    def __init__(
        self,
        raw: z3.BitVecRef,
        func_name: Optional[str],
        input_: "BitVec" = None,
        annotations: Optional[Annotations] = None,
        nested_functions: Optional[List["BitVecFunc"]] = None,
        concat_args: List = None,
        low=None,
        high=None,
        parent=None,
    ):
        """

        :param raw: The raw bit vector symbol
        :param func_name: The function name. e.g. sha3
        :param input: The input to the functions
        :param annotations: The annotations the BitVecFunc should start with
        """
        super().__init__(
            raw=raw,
            func_name=func_name,
            input_=input_,
            annotations=annotations,
            nested_functions=nested_functions,
            concat_args=concat_args,
        )
        self.low = low
        self.high = high
        self.parent = parent
