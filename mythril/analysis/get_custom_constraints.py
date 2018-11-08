import re
from z3 import *
from mythril.laser.ethereum.transaction import ContractCreationTransaction


def get_non_creator_constraints(state, node):
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
        if not _check_changeable_constraints(node.constraints):
            return [], True
    return not_creator_constraints, False


def _check_changeable_constraints(constraints):
    for constraint in constraints:
        if re.search(r"caller", str(constraint)) and re.search(
            r"[0-9]{20}", str(constraint)
        ):
            return False
    return True
