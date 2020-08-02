from typing import Union
import z3

from mythril.laser.smt.array import Array


def z3_array_converter(array: Union[z3.Array, z3.K]):
    new_array = Array(
        "name_to_be_overwritten", array.domain().size(), array.range().size()
    )
    new_array.raw = array
    return new_array
