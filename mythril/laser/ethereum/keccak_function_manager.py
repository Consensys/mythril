from random import randint

from ethereum import utils
from mythril.laser.smt import (
    BitVec,
    Function,
    URem,
    symbol_factory,
    ULE,
    And,
    ULT,
    Or,
    simplify,
    Extract,
)

TOTAL_PARTS = 10 ** 40
PART = (2 ** 256 - 1) // TOTAL_PARTS
INTERVAL_DIFFERENCE = 10 ** 30


class KeccakFunctionManager:
    def __init__(self):
        self.sizes = {}
        self.size_index = {}
        self.index_counter = TOTAL_PARTS - 34534
        self.keccak_parent = {}
        self.size_values = {}
        self.keccak_vals = {}
        self.delete_constraints = []

    def find_keccak(self, data: BitVec) -> BitVec:
        keccak = symbol_factory.BitVecVal(
            int.from_bytes(
                utils.sha3(data.value.to_bytes(data.size() // 8, byteorder="big")),
                "big",
            ),
            256,
        )
        func, _ = self.sizes[data.size()]
        self.keccak_vals[func(data)] = keccak
        return keccak

    def create_keccak(self, data: BitVec, length: int, global_state):
        length = length * 8
        data = simplify(data)
        if data.symbolic and simplify(data) not in global_state.topo_keys:
            if data.size() != 512:
                self.keccak_parent[data] = None
                global_state.topo_keys.append(simplify(data))
            else:
                p1 = simplify(Extract(511, 256, data))
                if p1.symbolic and p1 not in global_state.topo_keys:
                    global_state.topo_keys.append(p1)
                    self.keccak_parent[p1] = None

        assert length == data.size()
        constraints = []
        try:
            func, inverse = self.sizes[length]
        except KeyError:
            func = Function("keccak256_{}".format(length), length, 256)
            inverse = Function("keccak256_{}-1".format(length), 256, length)
            self.sizes[length] = (func, inverse)
            self.size_values[length] = []

        constraints.append(inverse(func(data)) == data)

        if data.symbolic is False:
            keccak = self.find_keccak(data)
            self.size_values[length].append(keccak)
            constraints.append(func(data) == keccak)
            return func(data), constraints

        if simplify(func(data)) not in global_state.topo_keys:
            self.keccak_parent[simplify(func(data))] = data
            global_state.topo_keys.append(simplify(func(data)))

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
            URem(func(data), symbol_factory.BitVecVal(64, 256)) == 0,
        )

        for val in self.size_values[length]:
            if hash(simplify(func(data))) != hash(simplify(val)):
                condition = Or(condition, func(data) == val)
        self.delete_constraints.append(condition)

        constraints.append(condition)
        if func(data) not in self.size_values[length]:
            self.size_values[length].append(func(data))
        return func(data), constraints


keccak_function_manager = KeccakFunctionManager()
