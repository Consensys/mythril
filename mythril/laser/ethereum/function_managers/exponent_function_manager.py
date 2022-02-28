import logging
from typing import Tuple


from mythril.laser.smt import And, BitVec, Bool, Function, URem, symbol_factory

log = logging.getLogger(__name__)


class ExponentFunctionManager:
    """
    Uses an uninterpreted function for exponentiation with the following properties:
    1) power(a, b) > 0
    2) if a = 256 => forall i if b = i then power(a, b) = (256 ^ i) % (2^256)

    Only these two properties are added as to handle indexing of boolean arrays.
    Caution should be exercised when increasing the conditions since it severely affects
    the solving time.
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
        """
        Creates a condition for exponentiation
        :param base: The base of exponentiation
        :param exponent: The exponent of the exponentiation
        :return: Tuple of condition and the exponentiation result
        """
        power = Function("Power", [256, 256], 256)
        exponentiation = power(base, exponent)

        if exponent.symbolic is False and base.symbolic is False:
            const_exponentiation = symbol_factory.BitVecVal(
                pow(base.value, exponent.value, 2 ** 256),
                256,
                annotations=base.annotations.union(exponent.annotations),
            )
            constraint = const_exponentiation == exponentiation
            return const_exponentiation, constraint

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

        return exponentiation, constraint


exponent_function_manager = ExponentFunctionManager()
