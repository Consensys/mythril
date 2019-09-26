from copy import copy
from ethereum import utils
from mythril.laser.smt import (
    BitVec,
    Bool,
    Expression,
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
        self.get_function = {}
        self.interval_hook_for_size = {}
        self.keccak_parent = {}
        self.values_for_size = {}
        self.delete_constraints = []
        self.flag_conditions = {}
        self.value_inverse = {}
        self._index_counter = TOTAL_PARTS - 34534

    def find_keccak(self, data: BitVec) -> BitVec:
        keccak = symbol_factory.BitVecVal(
            int.from_bytes(
                utils.sha3(data.value.to_bytes(data.size() // 8, byteorder="big")),
                "big",
            ),
            256,
        )
        func, _ = self.get_function[data.size()]
        return keccak

    def create_keccak(self, data: BitVec, global_state):

        length = data.size()
        simplify(data)
        if data.symbolic and data not in global_state.topo_keys:
            # New keccak
            if data.size() != 512:
                self.keccak_parent[data] = None
                global_state.topo_keys.append(data)
            else:
                # size of 512 usually means Concat(key, storage_slot_for_that_var)
                # This is solidity specific stuff :(
                p1 = simplify(Extract(511, 256, data))
                if p1.symbolic and p1 not in global_state.topo_keys:
                    global_state.topo_keys.append(p1)
                    self.keccak_parent[p1] = None

        constraints = []
        try:
            func, inverse = self.get_function[length]
        except KeyError:
            func = Function("keccak256_{}".format(length), length, 256)
            inverse = Function("keccak256_{}-1".format(length), 256, length)
            self.get_function[length] = (func, inverse)
            self.values_for_size[length] = []
        flag_var = symbol_factory.BoolSym("{}_flag".format(hash(simplify(func(data)))))

        constraints.append(inverse(func(data)) == data)

        if data.symbolic is False:
            keccak = self.find_keccak(data)
            self.values_for_size[length].append(keccak)
            constraints.append(func(data) == keccak)
            constraints.append(flag_var)
            return keccak, constraints

        if simplify(func(data)) not in global_state.topo_keys:
            self.keccak_parent[simplify(func(data))] = data
            global_state.topo_keys.append(simplify(func(data)))

        try:
            index = self.interval_hook_for_size[length]
        except KeyError:
            self.interval_hook_for_size[length] = self._index_counter
            index = self._index_counter
            self._index_counter -= INTERVAL_DIFFERENCE

        lower_bound = index * PART
        upper_bound = lower_bound + PART

        condition = And(
            ULE(symbol_factory.BitVecVal(lower_bound, 256), func(data)),
            ULT(func(data), symbol_factory.BitVecVal(upper_bound, 256)),
            URem(func(data), symbol_factory.BitVecVal(64, 256)) == 0,
        )
        f_cond = copy(condition)
        flag_condition = symbol_factory.Bool(False)
        total_keys = global_state.total_topo_keys
        for val in self.values_for_size[length]:
            if (
                hash(simplify(func(data))) == hash(simplify(val))
                or val not in total_keys
            ):
                continue

            other_keccak_condion = And(
                func(data) == val, inverse(func(data)) == inverse(val)
            )
            if val.value:
                val_inverse = self.value_inverse[val]
                flag_var2 = self.get_flag(val_inverse)

                other_keccak_condion = And(other_keccak_condion, flag_var, flag_var2)
            else:
                iter_val_flag_var = self.get_flag(simplify(val))
                other_keccak_condion = And(
                    other_keccak_condion, iter_val_flag_var, flag_var
                )

            condition = Or(condition, other_keccak_condion)
            flag_condition = Or(flag_condition, other_keccak_condion)

        self.flag_conditions[func(data)] = (f_cond, flag_condition, None)
        self.delete_constraints.append(condition)

        constraints.append(condition)
        if func(data) not in self.values_for_size[length]:
            self.values_for_size[length].append(func(data))

        return func(data), constraints

    def get_flag(self, val: Expression) -> Bool:
        return symbol_factory.BoolSym("{}_flag".format(hash(simplify(val))))


keccak_function_manager = KeccakFunctionManager()
