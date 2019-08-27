from ethereum import utils
from mythril.laser.smt import BitVec, Function, URem, symbol_factory, ULE, And, ULT, Or

TOTAL_PARTS = 10 ** 40
PART = (2 ** 256 - 1) // TOTAL_PARTS
INTERVAL_DIFFERENCE = 10 ** 30


class KeccakFunctionManager:
    def __init__(self):
        self.sizes = {}
        self.size_index = {}
        self.index_counter = TOTAL_PARTS - 34534
        self.size_values = {}

    def create_keccak(self, data: BitVec, length: int):
        length = length * 8
        assert length == data.size()
        try:
            func, inverse = self.sizes[length]
        except KeyError:
            func = Function("keccak256_{}".format(length), length, 256)
            inverse = Function("keccak256_{}-1".format(length), 256, length)
            self.sizes[length] = (func, inverse)
            self.size_values[length] = []
        constraints = []
        if data.symbolic is False:
            keccak = symbol_factory.BitVecVal(
                utils.sha3(data.value.to_bytes(length // 8, byteorder="big")), 256
            )
            constraints.append(func(data) == keccak)

        constraints.append(inverse(func(data)) == data)
        if data.symbolic is False:
            return func(data), constraints

        constraints.append(URem(func(data), symbol_factory.BitVecVal(63, 256)) == 0)
        try:
            index = self.size_index[length]
        except KeyError:
            self.size_index[length] = self.index_counter
            index = self.index_counter
            self.index_counter -= INTERVAL_DIFFERENCE

        lower_bound = index * PART
        upper_bound = (index + 1) * PART

        condition = And(
            ULE(symbol_factory.BitVecVal(lower_bound, 256), func(data)),
            ULT(func(data), symbol_factory.BitVecVal(upper_bound, 256)),
        )
        for val in self.size_values[length]:
            condition = Or(condition, func(data) == val)
        constraints.append(condition)
        return func(data), constraints


keccak_function_manager = KeccakFunctionManager()
