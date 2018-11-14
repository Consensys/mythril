import re
from typing import List
from z3 import *
from mythril.laser.ethereum.transaction import ContractCreationTransaction
from mythril.laser.ethereum.state.global_state import GlobalState


def get_non_creator_constraints(state: GlobalState) -> (List, bool):
    """
    Get constraints which say that the caller isn't the creator of the contract
    :param state: The state
    :return: tuple of (constraints, bool) where the bool says whether the caller is constrained or not
    """
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
        if not has_caller_check_constraint(state.mstate.constraints):
            return [], True
    return not_creator_constraints, False


def has_caller_check_constraint(constraints: List) -> bool:
    """
    Checks whether the caller is constrained to a value or not
    """
    for constraint in constraints:
        if re.search(r"caller", str(constraint)) and re.search(
            r"[0-9]{20}", str(constraint)
        ):
            return False
    return True
