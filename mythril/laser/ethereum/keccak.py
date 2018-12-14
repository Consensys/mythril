"""This module contains a function manager to deal with symbolic Keccak values."""
from mythril.laser.smt import Expression


class KeccakFunctionManager:
    """A keccak function manager for symbolic expressions."""
    def __init__(self):
        """

        """
        self.keccak_expression_mapping = {}

    def is_keccak(self, expression: Expression) -> bool:
        """

        :param expression:
        :return:
        """
        return str(expression) in self.keccak_expression_mapping.keys()

    def get_argument(self, expression: str) -> Expression:
        """

        :param expression:
        :return:
        """
        if not self.is_keccak(expression):
            raise ValueError("Expression is not a recognized keccac result")
        return self.keccak_expression_mapping[str(expression)][1]

    def add_keccak(self, expression: Expression, argument: Expression) -> None:
        """

        :param expression:
        :param argument:
        """
        index = str(expression)
        self.keccak_expression_mapping[index] = (expression, argument)
