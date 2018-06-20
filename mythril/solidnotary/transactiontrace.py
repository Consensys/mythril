from z3 import *
from copy import deepcopy
import re
from mythril.solidnotary.z3utility import are_satisfiable, simplify_constraints

"""
    Returns whether or the specified symbolic string stands for a data value that can be different from transaction to 
    transaction without the need of an intermediate call to the contract (e.g. a transaction params, blocknumber, ...)
"""


def is_t_variable(var):
    var = str(var)
    if (var.startswith("caller")
        or var.startswith("gasprice")
        or var.startswith("callvalue")
        or var.startswith("origin")
        or var.startswith("calldata_")
        or var.startswith("calldatasize_")
        or var.startswith("balance_at")
        or var.startswith("KECCAC_mem_")
        or var.startswith("keccac_")
        or var.startswith("gasprice")
        or var.startswith("extcodesize")
        or var.startswith("returndatasize")
        # or var.startswith(var, "blockhash_block_") should not change between transactions
        or var.startswith("coinbase")
        or var.startswith("timestamp")
        or var.startswith("block_number")
        or var.startswith("block_difficulty")
        or var.startswith("block_gaslimit")
        or var.startswith("mem_")
        or var.startswith("msize")
        or var.startswith("gas")
        or var.startswith("retval_")
        or var.startswith("keccac_")):
        return True
    else:
        return False


def filter_for_t_variable_data(sym_vars):
    return list(filter(lambda x: is_t_variable(x), sym_vars))

class TransactionTrace:

    def __init__(self, storage, constraints, lvl=1):
        self.storage = storage # Todo give all non storage symbolic values that can be different every transaction the number one
        self.constraints = constraints # Todo eliminate all constraints that are not regarding the beginning of the transaction may not be necessary
        # eliminate all constraints that only contain names not in the set of names from storage
        self.constraints = simplify_constraints(self.constraints) # Todo simplification of the sum of constraints
        self.tran_constraints = deepcopy(self.constraints)
        self.lvl = lvl
        self.sym_names = self.extract_sym_names_from_storage()
        self.sym_names.extend(self.extract_sym_names_from_constraints())
        if lvl == 1:
            self.set_transaction_idx()

        # Todo the constraints of a trace are probably also important here and have to be somehow aggregated
        # Todo Identifiy addional trace information such as blocknumber and more

    def __str__(self):
        return str(self.as_dict())

    def as_dict(self):

        return {'lvl': self.lvl, 'storage': str(self.storage), 'constraints': str(self.constraints)}

    def pp_trace(self):
        print()
        print("Trace lvl: {}".format(self.lvl))
        print("Storage: {}".format({k: str(v).replace("\n", " ") for k, v in self.storage.items()}))
        print("Constraints: {}".format(list(map(lambda x: str(x).replace("\n", " "), self.constraints))))
        print()


    def add_transaction_idx(self, offset):
        new_names = []
        for name in self.sym_names:
            matched_name = re.search(r't([0-9]+)(_.*)', name)
            num = int(matched_name.group(1)) + offset
            new_names.append("t" + str(num) + matched_name.group(2))
        repl_tup = list(zip(self.sym_names, new_names))

        self.substitute_bv_names(repl_tup)

        self.sym_names = new_names

    def set_transaction_idx(self):
        repl_tup = []
        new_sym_names = []
        for name in self.sym_names:
            repl_tup.append((name, "t1_" + name))
            new_sym_names.append("t1_" + name)
        self.sym_names = new_sym_names
        self.substitute_bv_names(repl_tup)

    def substitute_bv_names(self, subs_tuple):
        subs_tuples = list(map(lambda name_t: (BitVec(name_t[0], 256), BitVec(name_t[1], 256)), subs_tuple))
        for s_num, slot in self.storage.items():
            self.storage[s_num] = substitute(slot, subs_tuples)
        for c_idx in range(len(self.constraints)):
            self.constraints[c_idx] = substitute(self.constraints[c_idx], subs_tuples)

    def extract_sym_names(self, obj):
        if (not hasattr(obj, 'children') or len(obj.children()) == 0) and hasattr(obj, 'decl') :
                return [str(obj.decl())]
        else:
            sym_vars = []
            for c in obj.children():
                sym_vars.extend(self.extract_sym_names(c))
            return sym_vars

    def extract_sym_names_from_constraints(self):
        sym_names = []
        for k,v in self.storage.items():
            sym_names.extend(self.extract_sym_names(v))
        return filter_for_t_variable_data(sym_names)

    def extract_sym_names_from_storage(self):
        sym_names = []
        for v in self.constraints:
            sym_names.extend(self.extract_sym_names(v))
        return filter_for_t_variable_data(sym_names) # Todo Check whether here it is the right choice too, to filter ...

    """
          Either do only deep checing here and use the proper trace or storage_slot reduction in the apply function. Or do
          both here.
      """

    def deep_equals(trace_lvl1, trace_lvl2):
        return set(trace_lvl1) == set(trace_lvl2) # Todo Impelement an ACTUAL deep comparison

    def simplify_storage(self):
        for k,v in self.storage.items():
            # Todo explore the arguments of this storage simplification in z3 to find ways to further simplify and to
            # sort this expressions for equality comparison
            self.storage[k] = simplify(v)

    """
        Applies the new trace tt on a possibly even changed trace self.
    """
    def apply_trace(self, tt):
        if tt is None:
            return self
        new_trace = deepcopy(tt)
        new_trace.add_transaction_idx(self.lvl)
        subs_map = list(map(lambda x: (BitVec("storage_" + str(x[0]), 256), x[1]), self.storage.items()))
        for k,v in new_trace.storage.items():
            new_trace.storage[k] = substitute(v, subs_map)
        for c_idx in range(len(new_trace.constraints)):
            new_trace.constraints[c_idx] = substitute(new_trace.constraints[c_idx], subs_map)
        new_trace.lvl += self.lvl
        new_trace.sym_names.extend(deepcopy(self.sym_names))
        # self can be omitted (e.g. when related storage locations were overwritten)
        new_trace.simplify_storage()
        new_trace.constraints = simplify_constraints(new_trace.constraints)
        # Simplify constraints in there sum to eliminate subconstraints
        if are_satisfiable(new_trace.constraints):
            return new_trace
        else:
            return None

    def apply_traces_parallel(self, traces):
        combined_traces = []
        for trace in traces:
            combined_traces.append(self.apply_trace(trace))
        return list(filter(lambda t: not t is None, combined_traces))

    def apply_exact_trace_levels(self, traces, depth):
        # Todo maybe some faster trace build not building one level at a time to e.g.
        # Todo reach level 17 but build 2, then 4, then 8 and then 16 then 17
        trace_lvl_n = [self]
        for i in range(depth):
            trace_lvl_np1 = []
            for trace in trace_lvl_n:
                trace_lvl_np1.extend(trace.apply_traces_parallel(traces))
            if TransactionTrace.deep_equals(trace_lvl_np1, trace_lvl_n): # Fixpoint detected, function needs to ignore lists, dicts and objects.
                return trace_lvl_n
            trace_lvl_n = trace_lvl_np1
        return trace_lvl_n

    def apply_up_to_trace_levels(self, traces, depth):
        traces_up_to = [[self]] # elements are trace_levels
        for i in range(depth):
            trace_lvl_np1 = []
            for trace in traces_up_to[-1]:
                trace_lvl_np1.extend(trace.apply_traces_parallel(traces))
            for trace_lvl_i in traces_up_to:
                # the following might be faster to check when using a content representing hash
                if TransactionTrace.deep_equals(trace_lvl_np1, trace_lvl_i): # cycle in the traces of trace chains detected: levels
                    # while repeat themselves, function needs to ignore lists, dicts and objects.
                    return traces_up_to
            traces_up_to.append(trace_lvl_np1)
        return traces_up_to

    # Todo Maybe implement a function that checks whether two traces are combinable before creating objekts, adv. in
    # case they are not the object creation doe not have to be done. Investigate whether a suicide trace completely
    # stopes the contract from being executable. In that case a suicided transaction also is not combinable with
    # successive transactions.

    # Todo write a function that allows to specify a function/invocable to explore the tracechain space in DFS manner


