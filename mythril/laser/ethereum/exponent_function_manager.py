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
        power = Function("Power", [256, 256], 256)
        NUMBER_256 = symbol_factory.BitVecVal(256, 256)
        self.concrete_constraints = And(
            *[
                power(NUMBER_256, symbol_factory.BitVecVal(i, 256))
                == symbol_factory.BitVecVal(256 ** i, 256)
                for i in range(0, 32)
            ]
        )
        self.concrete_constraints_sent = False

    def create_condition(self, base: BitVec, exponent: BitVec) -> Tuple[BitVec, Bool]:
        power = Function("Power", [256, 256], 256)
        exponentiation = power(base, exponent)
        constraint = exponentiation > 0
        if self.concrete_constraints_sent is False:
            constraint = And(constraint, self.concrete_constraints)
            self.concrete_constraints_sent = True
        if base.value == 256:
            constraint = And(
                constraint,
                power(base, URem(exponent, symbol_factory.BitVecVal(32, 256)))
                == power(base, exponent),
            )

        if exponent.symbolic is False and base.symbolic is False:
            const_exponentiation = symbol_factory.BitVecVal(
                pow(base.value, exponent.value, 2 ** 256),
                256,
                annotations=base.annotations.union(exponent.annotations),
            )
            constraint = And(constraint, const_exponentiation == exponentiation)
            return const_exponentiation, constraint
        return exponentiation, constraint


exponent_function_manager = ExponentFunctionManager()
