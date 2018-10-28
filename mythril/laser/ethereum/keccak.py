from z3 import ExprRef, BitVecRef



class KeccakFunctionManager:
    def __init__(self):
        self.keccak_expression_mapping = {}

    def is_keccak(self, expression: BitVecRef) -> bool:
        return str(expression) in self.keccak_expression_mapping.keys()

    def get_argument(self, expression: str) -> ExprRef:
        if not self.is_keccak(expression):
            raise ValueError("Expression is not a recognized keccac result")
        return self.keccak_expression_mapping[str(expression)][1]

    def add_keccak(self, expression: ExprRef, argument: ExprRef) -> None:
        index = str(expression)
        self.keccak_expression_mapping[index] = (expression, argument)
