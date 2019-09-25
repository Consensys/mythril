from random import randint

from copy import copy
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
    Implies,
    Not,
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
        self.keys = []
        self.flag_conditions = {}
        self.value_inverse = {}

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
        flag_var = symbol_factory.BoolSym("{}_flag".format(hash(simplify(func(data)))))

        constraints.append(inverse(func(data)) == data)

        if data.symbolic is False:
            keccak = self.find_keccak(data)
            self.size_values[length].append(keccak)
            constraints.append(func(data) == keccak)
            constraints.append(flag_var)
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
        f_cond = copy(condition)
        flag_condition = False
        total_keys = global_state.total_topo_keys
        for val in self.size_values[length]:
            if hash(simplify(func(data))) != hash(simplify(val)) and val in total_keys:
                prev_flag_var = symbol_factory.BoolSym(
                    "{}_flag".format(hash(simplify(val)))
                )
                pre_cond = And(func(data) == val, inverse(func(data)) == inverse(val))
                if val.value:
                    k2 = self.value_inverse[val]
                    flag_var2 = symbol_factory.BoolSym(
                        "{}_flag".format(hash(simplify(k2)))
                    )

                    pre_cond = And(pre_cond, flag_var, flag_var2)
                else:
                    pre_cond = And(pre_cond, prev_flag_var, flag_var)

                condition = Or(condition, pre_cond)
                flag_condition = Or(flag_condition, pre_cond)

        self.flag_conditions[func(data)] = (f_cond, flag_condition, None)
        self.delete_constraints.append(condition)

        constraints.append(condition)
        if func(data) not in self.size_values[length]:
            self.size_values[length].append(func(data))
        if data not in self.keys:
            self.keys.append(data)
        if func(data) not in self.keys:
            self.keys.append(func(data))

        return func(data), constraints


keccak_function_manager = KeccakFunctionManager()
