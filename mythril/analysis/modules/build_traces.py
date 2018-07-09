from mythril.analysis.report import Issue
from mythril.solidnotary.transactiontrace import TransactionTrace
from mythril.disassembler.disassembly import Disassembly
from laser.ethereum.svm import GlobalState, Account, Environment, MachineState, CalldataType
from z3 import BitVec
from mythril.analysis.symbolic import SymExecWrapper
from mythril.solidnotary.solidnotary import get_transaction_traces, get_construction_traces
from mythril.solidnotary.z3utility import  are_satisfiable
import logging
from mythril.solidnotary.calldata import get_minimal_constructor_param_encoding_len, abi_json_to_abi


'''
    Build execution traces from the statespace 
'''

def print_obj(obj):
    print()
    print(type(obj))
    print(obj)
    print(dir(obj))
    print(obj.decl())
    print(obj.params())
    print(obj.children())
    print()

def get_constr_glbstate(contract, address):

    mstate = MachineState(gas=10000000)

    minimal_const_byte_len = get_minimal_constructor_param_encoding_len(abi_json_to_abi(contract.abi))

    # better would be to append symbolic params to the bytecode such that the codecopy instruction that copies the
    # params into memory takes care of placing them onto the memory with the respective size.
    for i in range(int(minimal_const_byte_len / 32)):
        mstate.mem_extend(128 + 32 * i, 32)
        mstate.memory.insert(128 + 32 * i, BitVec('calldata_' + contract.name + '_' + str(i * 32), 256))

    # Todo Replace pure placement of enough symbolic 32 Byte-words with placement of symbolic variables that contain
    # the name of the solidity variables

    accounts = {address: Account(address, contract.disassembly, contract_name=contract.name)}

    environment = Environment(
        accounts[address],
        BitVec("caller", 256),
        [],
        BitVec("gasprice", 256),
        BitVec("callvalue", 256),
        BitVec("origin", 256),
        calldata_type=CalldataType.SYMBOLIC,
    )

    # Todo find source for account info, maybe the std statespace?

    return GlobalState(accounts, environment, mstate)


def execute(statespace):

    logging.debug("Executing module: Transaction End")

    constructor_trace = {}

    if hasattr(statespace, "sym_constr"):
        sym_exe_tuple = statespace.sym_constr
        glbstate = get_constr_glbstate(sym_exe_tuple[0], sym_exe_tuple[1])
        sym_exe_tuple = statespace.sym_constr + (glbstate,)
        constr_statespace = SymExecWrapper(*sym_exe_tuple)
        constructor_trace = get_construction_traces(constr_statespace) # Todo the traces here should not contain references to storages anymore
        for t in constructor_trace:
            t.pp_trace()

    traces = get_transaction_traces(statespace)
    for trace in constructor_trace:
        comp_trace_lvls = trace.apply_up_to_trace_levels(traces, 3)
        for trace_lvl in comp_trace_lvls:
            for t in trace_lvl:
                    t.pp_trace()

    # for trace in traces:
    #    trace.pp_trace()

    #print("==== Second level traces ====")
    #for trace in traces:
    #    comp_trace_lvls = trace.apply_up_to_trace_levels(traces, 1)
        #for trace_lvl in range(len(comp_trace_lvls)):
            # print("\nTrace level: " + str(trace_lvl))
            #for comp_trace in comp_trace_lvls[trace_lvl]:
            #    print(comp_trace.storage)
                # for k, s in comp_trace.storage.items():
                #    print_obj(s)

    return []
