from mythril.analysis import solver
from mythril.analysis.ops import *
from mythril.analysis.report import Issue
from mythril.analysis.swc_data import UNPROTECTED_SELFDESTRUCT
from mythril.exceptions import UnsatError
from mythril.laser.ethereum.transaction import ContractCreationTransaction
import re
import logging


"""
MODULE DESCRIPTION:

Check for SUICIDE instructions that either can be reached by anyone, or where msg.sender is checked against a tainted storage index 
(i.e. there's a write to that index is unconstrained by msg.sender).
"""


def execute(state_space):

    logging.debug("Executing module: UNCHECKED_SUICIDE")

    issues = []

    for k in state_space.nodes:
        node = state_space.nodes[k]

        for state in node.states:
            issues += _analyze_state(state, node)

    return issues


def _analyze_state(state, node):
    issues = []
    instruction = state.get_current_instruction()

    if instruction["opcode"] != "SUICIDE":
        return []

    to = state.mstate.stack[-1]

    logging.debug("[UNCHECKED_SUICIDE] suicide in function " + node.function_name)

    description = "A reachable SUICIDE instruction was detected. "

    if "caller" in str(to):
        description += "The remaining Ether is sent to the caller's address.\n"
    elif "storage" in str(to):
        description += "The remaining Ether is sent to a stored address.\n"
    elif "calldata" in str(to):
        description += "The remaining Ether is sent to an address provided as a function argument.\n"
    elif type(to) == BitVecNumRef:
        description += "The remaining Ether is sent to: " + hex(to.as_long()) + "\n"
    else:
        description += "The remaining Ether is sent to: " + str(to) + "\n"

    not_creator_constraints = []
    creator = None
    if isinstance(
        state.world_state.transaction_sequence[0], ContractCreationTransaction
    ):
        creator = state.world_state.transaction_sequence[0].caller
    if creator is not None:
        for transaction in state.world_state.transaction_sequence[1:]:
            not_creator_constraints.append(
                Not(Extract(159, 0, transaction.caller) == Extract(159, 0, creator))
            )
            not_creator_constraints.append(
                Not(Extract(159, 0, transaction.caller) == 0)
            )
    else:
        for transaction in state.world_state.transaction_sequence:
            not_creator_constraints.append(
                Not(Extract(159, 0, transaction.caller) == 0)
            )
        if not check_changeable_constraints(node.constraints):
            return []

    try:
        model = solver.get_model(node.constraints + not_creator_constraints)

        debug = "Transaction Sequence: " + str(
            solver.get_transaction_sequence(
                state, node.constraints + not_creator_constraints
            )
        )

        issue = Issue(
            contract=node.contract_name,
            function_name=node.function_name,
            address=instruction["address"],
            swc_id=UNPROTECTED_SELFDESTRUCT,
            bytecode=state.environment.code.bytecode,
            title="Unchecked SUICIDE",
            _type="Warning",
            description=description,
            debug=debug,
            gas_used=(state.mstate.min_gas_used, state.mstate.max_gas_used),
        )
        issues.append(issue)
    except UnsatError:
        logging.debug("[UNCHECKED_SUICIDE] no model found")

    return issues


def check_changeable_constraints(constraints):
    for constraint in constraints:
        if re.search(r"caller", str(constraint)) and re.search(
            r"[0-9]{20}", str(constraint)
        ):
            return False
    return True
