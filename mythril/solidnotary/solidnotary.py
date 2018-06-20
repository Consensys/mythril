import logging
from mythril.solidnotary.transactiontrace import TransactionTrace
from mythril.solidnotary.z3utility import are_satisfiable
from laser.ethereum.svm import Environment, GlobalState, CalldataType
from z3 import BitVec, simplify, is_false, is_bool, is_true, Solver, sat
from copy import deepcopy


class SolidNotary:

    def __init__(self):
        # Todo Parse Annotations and store them in an additional structure
        # Todo receive a list of files or a file, these are modified for the analysis
        pass

    def notarize(self):
        # Todo Instantiate an instance of Mythril, analyze and print the result
        # Todo Find how they are storing results
        pass

def get_transaction_traces(statespace):
    logging.debug("Executing module: Transaction End")

    traces = []

    for k in statespace.nodes:
        node = statespace.nodes[k]
        for state in node.states:
            instruction = state.get_current_instruction()
            if instruction['opcode'] == "STOP":
                if are_satisfiable(state.mstate.constraints):
                    traces.append(TransactionTrace(state.environment.active_account.storage, state.mstate.constraints))
    return traces

def get_t_indexed_environment(active_account, index):

        # Initialize the execution environment

        environment = Environment(
            active_account,
            BitVec("caller_"+str(index), 256),
            [],
            BitVec("gasprice_"+str(index), 256),
            BitVec("callvalue_"+str(index), 256),
            BitVec("origin_"+str(index), 256),
            calldata_type=CalldataType.SYMBOLIC,
        )

        return environment

def get_t_indexed_globstate(active_account, index):
    environment = get_t_indexed_environment(active_account, index)
    # Todo is this just some set of preset accounts? How should we deal with it
    return GlobalState(self.accounts, environment)

