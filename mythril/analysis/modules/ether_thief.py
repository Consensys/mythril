from mythril.analysis.ops import *
from mythril.analysis import solver
from mythril.analysis.analysis_utils import get_non_creator_constraints
from mythril.analysis.report import Issue
from mythril.analysis.swc_data import UNPROTECTED_ETHER_WITHDRAWAL
from mythril.exceptions import UnsatError
import logging


"""
MODULE DESCRIPTION:

Search for cases where Ether can be withdrawn to a user-specified address. 

An issue is reported ONLY IF:

- The transaction sender does not match contract creator;
- The sender has not previously sent any ETH to the contract account.

This is somewhat coarse and needs to be refined in the future.

"""


def execute(state_space):

    logging.debug("Executing module: ETHER_THIEF")

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

    not_creator_constraints, constrained = get_non_creator_constraints(state)
    if constrained:
        return []

    try:

        """
        FIXME: Instead of solving for call_value > 0, check whether call value can be greater than
        the total value of all transactions received by the caller
        """

        model = solver.get_model(
            node.constraints + not_creator_constraints + [call_value > 0]
        )

        transaction_sequence = solver.get_transaction_sequence(
            state, node.constraints + not_creator_constraints + [call_value > 0]
        )

        # For now we only report an issue if zero ETH has been sent to the contract account.

        for key, value in transaction_sequence.items():
            if int(value["call_value"], 16) > 0:
                return []

        debug = "Transaction Sequence: " + str(transaction_sequence)

        issue = Issue(
            contract=node.contract_name,
            function_name=node.function_name,
            address=instruction["address"],
            swc_id=UNPROTECTED_ETHER_WITHDRAWAL,
            title="Ether thief",
            _type="Warning",
            bytecode=state.environment.code.bytecode,
            description="Users other than the contract creator can withdraw ETH from the contract account"
            + " without previously having sent any ETH to it. This is likely to be vulnerability.",
            debug=debug,
        )
        issues.append(issue)
    except UnsatError:
        logging.debug("[ETHER_THIEF] no model found")

    return issues
