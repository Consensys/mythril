from mythril.analysis.ops import *
from mythril.analysis import solver
from mythril.analysis.report import Issue
from mythril.analysis.swc_data import UNPROTECTED_ETHER_WITHDRAWAL
from mythril.exceptions import UnsatError
import logging


'''
MODULE DESCRIPTION:

Check for CALLs that send >0 Ether to either the transaction sender, or to an address provided as a function argument.
Returns an issue if the state can be reached if msg.sender != creator.
'''


def execute(state_space):

    logging.debug("Executing module: ETHER_SEND")

    issues = []

    for k in state_space.nodes:
        node = state_space.nodes[k]

        for state in node.states:
            issues += _analyze_state(state, node)


def _analyze_state(state, node):
    issues = []
    instruction = state.get_current_instruction()

    if instruction['opcode'] != "CALL":
        return []

    call_value = state.mstate.stack[-3]
    target = state.mstate.stack[-2]

    not_creator_constraints = []
    if len(state.world_state.transaction_sequence) > 1:
        creator = state.world_state.transaction_sequence[0].caller
        for transaction in state.world_state.transaction_sequence[1:]:
            not_creator_constraints.append(Not(Extract(159, 0, transaction.caller) == Extract(159, 0, creator)))
            not_creator_constraints.append(Not(Extract(159, 0, transaction.caller) == 0))

    try:
        model = solver.get_model(node.constraints + not_creator_constraints + [call_value > 0])

        debug = "SOLVER OUTPUT:\n" + solver.pretty_print_model(model)

        issue = Issue(contract=node.contract_name, function=node.function_name, address=instruction['address'],
                      swc_id=UNPROTECTED_ETHER_WITHDRAWAL, title="Ether send", _type="Warning",
                      description="Ether can be extracted from the contract by addresses other than the contract creator.".format(target), debug=debug)
        issues.append(issue)
    except UnsatError:
        logging.debug("[UNCHECKED_ETHER] no model found")

    return issues
