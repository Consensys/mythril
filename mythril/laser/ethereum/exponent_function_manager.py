from ethereum import utils
from mythril.laser.smt import (
    BitVec,
    Extract,
    Function,
    URem,
    symbol_factory,
    ULE,
    And,
    ULT,
    UDiv,
    Bool,
    If,
    Or,
    Not,
)
from typing import Dict, Tuple, List, Optional

import logging

log = logging.getLogger(__name__)


class ExponentFunctionManager:
    """
    Uses an uninterpreted function for exponentiation with the following property
    exp(a, b) > 0
    if b > c ==> exp(a, b) > exp(a, c)
    exp(a, b) = exp(a, c) <=> b = c
    exp(a, b) = exp(c, b) <=> a = c
    """

    def __init__(self):
        self.exp_set: Set[List[BitVec, BitVec, BitVec]] = set()

    def create_condition(self, base: BitVec, exponent: BitVec) -> Tuple[BitVec, Bool]:
        power = Function("Power", [256, 256], 256)
        exponentiation = power(base, exponent)
        constraint = And(
            exponentiation >= 0,
            Or(
                And(power(base, exponent) == 1, exponent == 0),
                And(power(base, exponent) != 1, exponent != 0),
            ),
        )
        if base.value == 256:
            constraint = And(
                constraint, (Extract(7, 0, exponentiation) == 0) ^ (exponent == 0)
            )
        for a, b, c in self.exp_set:
            constraint = And(
                constraint, Or(c != exponentiation, Not((a == base) ^ (b == exponent)))
            )
            if base.value != a.value:
                continue
            equivalent_division = And(
                Or(
                    And(power(a, b - exponent) == 1, b - exponent == 0),
                    And(power(a, b - exponent) != 1, b - exponent != 0),
                ),
                UDiv(exponentiation, power(a, b)) == power(a, exponent - b),
                UDiv(power(a, b), exponentiation) == power(a, b - exponent),
                Or(
                    And(exponent > b, exponentiation > power(a, b)),
                    And(exponent <= b, exponentiation <= power(a, b)),
                ),
            )
            constraint = And(constraint, equivalent_division)
            if base.value == 256:
                constraint = And(
                    constraint,
                    (Extract(7, 0, power(a, exponent - b)) == 0) ^ (exponent == b),
                    (Extract(7, 0, power(a, b - exponent)) == 0) ^ (exponent == b),
                )

        self.exp_set.add((base, exponent, exponentiation))
        if exponent.symbolic is False and base.symbolic is False:
            const_exponentiation = symbol_factory.BitVecVal(
                pow(base.value, exponent.value, 2 ** 256),
                256,
                annotations=base.annotations.union(exponent.annotations),
            )
            constraint = And(constraint, const_exponentiation == exponentiation)
        return exponentiation, constraint


exponent_function_manager = ExponentFunctionManager()
