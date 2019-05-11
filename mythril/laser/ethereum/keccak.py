"""This module contains a function manager to deal with symbolic Keccak
values."""
from mythril.laser.smt import Expression, BitVecFunc, BitVec
from typing import cast, Union


class KeccakFunctionManager:
    """A keccak function manager for symbolic expressions."""

    def __init__(self):
        """"""
        self.keccak_expression_mapping = {}

    def is_keccak(self, expression: Expression) -> bool:
        """

        :param expression:
        :return:
        """
        if not isinstance(expression, BitVecFunc):
            return False
        return expression.func_name == "keccak256"

    def get_argument(self, expression: Expression) -> Expression:
        """

        :param expression:
        :return:
        """
        if not self.is_keccak(expression):
            raise ValueError("Expression is not a recognized keccac result")
        return cast(BitVecFunc, expression).input_
