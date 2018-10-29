from mythril.analysis.ops import *
from mythril.analysis import solver
from mythril.analysis.report import Issue
from mythril.analysis.swc_data import UNPROTECTED_ETHER_WITHDRAWAL
from mythril.exceptions import UnsatError
import logging


"""
MODULE DESCRIPTION:

Check for CALLs that send >0 Ether to either the transaction sender, or to an address provided as a function argument.
If msg.sender is checked against a value in storage, check whether that storage index is tainted (i.e. there's an unconstrained write
to that index).
"""


def execute(state_space):

    logging.debug("Executing module: ETHER_SEND")

    issues = []

    for k in state_space.nodes:
        node = state_space.nodes[k]

        for state in node.states:
            issues += _analyze_state(state, node)

    return issues


def _analyze_state(state, node):
    issues = []
    instruction = state.get_current_instruction()

    if instruction["opcode"] != "CALL":
        return []

    call_value = state.mstate.stack[-3]
    target = state.mstate.stack[-2]

    not_creator_constraints = []
    if len(state.world_state.transaction_sequence) > 1:
        creator = state.world_state.transaction_sequence[0].caller
        for transaction in state.world_state.transaction_sequence[1:]:
            not_creator_constraints.append(
                Not(Extract(159, 0, transaction.caller) == Extract(159, 0, creator))
            )
            not_creator_constraints.append(
                Not(Extract(159, 0, transaction.caller) == 0)
            )

    try:
        model = solver.get_model(
            node.constraints + not_creator_constraints + [call_value > 0]
        )

        debug = "Transaction Sequence: " + str(
            solver.get_transaction_sequence(
                state, node.constraints + not_creator_constraints + [call_value > 0]
            )
        )

        issue = Issue(
            contract=node.contract_name,
            function=node.function_name,
            address=instruction["address"],
            swc_id=UNPROTECTED_ETHER_WITHDRAWAL,
            title="Ether send",
            _type="Warning",
            description="It seems that an attacker is able to execute an call instruction,"
            " this can mean that the attacker is able to extract funds "
            "out of the contract.".format(target),
            debug=debug,
        )
        issues.append(issue)
    except UnsatError:
        logging.debug("[UNCHECKED_SUICIDE] no model found")

    return issues
