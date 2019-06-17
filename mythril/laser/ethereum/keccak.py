"""This module contains a function manager to deal with symbolic Keccak
values."""
from mythril.laser.smt import Expression, BitVecFunc, BitVec
from typing import cast, Union


class KeccakFunctionManager:
    """A keccak function manager for symbolic expressions."""

    @staticmethod
    def is_keccak(expression: Expression) -> bool:
        """

        :param expression:
        :return:
        """
        if not isinstance(expression, BitVecFunc):
            return False
        return expression.func_name == "keccak256"

    @staticmethod
    def get_argument(expression: BitVec) -> BitVec:
        """

        :param expression:
        :return:
        """
        if not KeccakFunctionManager.is_keccak(expression):
            raise ValueError("Expression is not a recognized keccak result")
        return cast(BitVecFunc, expression).input_
