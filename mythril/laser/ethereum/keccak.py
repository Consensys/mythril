from mythril.laser.ethereum.smt_wrapper import Types

class KeccakFunctionManager:
    def __init__(self):
        self.keccak_expression_mapping = {}

    def is_keccak(self, expression) -> bool:
        return str(expression) in self.keccak_expression_mapping.keys()

    def get_argument(self, expression) -> Types.Expr:
        if not self.is_keccak(expression):
            raise ValueError("Expression is not a recognized keccac result")
        return self.keccak_expression_mapping[str(expression)][1]

    def add_keccak(self, expression: Types.Expr, argument: Types.Expr):
        index = str(expression)
        self.keccak_expression_mapping[index] = (expression, argument)
