import logging
from mythril.laser.ethereum.cfg import Node
from mythril.laser.ethereum.state.world_state import WorldState
from mythril.laser.ethereum.state.account import Account
from mythril.laser.ethereum.state.constraints import Constraints
from mythril.laser.smt import Not

CONSTRAINT_DIFFERENCE_LIMIT = 15

log = logging.getLogger(__name__)


def check_node_merge_condition(node1: Node, node2: Node):
    """
    Checks whether two nodes are merge-able
    :param node1: The node to be merged
    :param node2: The other node to be merged
    :return: Boolean, True if we can merge
    """
    return all(
        [
            node1.function_name == node2.function_name,
            node1.contract_name == node2.contract_name,
            node1.start_addr == node2.start_addr,
        ]
    )


def check_account_merge_condition(account1: Account, account2: Account):
    """
    Checks whether we can merge accounts
    """
    return all(
        [
            account1.nonce == account2.nonce,
            account1.deleted == account2.deleted,
            account1.code.bytecode == account2.code.bytecode,
        ]
    )


def check_ws_merge_condition(state1: WorldState, state2: WorldState):
    """
    Checks whether we can merge these states
    """
    if state1.node and not check_node_merge_condition(state1.node, state2.node):
        return False

    for address, account in state2.accounts.items():
        if (
            address in state1._accounts
            and check_account_merge_condition(state1._accounts[address], account)
            is False
        ):
            return False
    if not _check_merge_annotations(state1, state2):
        return False

    return True


def _check_merge_annotations(state1: WorldState, state2: WorldState):
    """
    Checks whether two annotations can be merged
    :param state:
    :return:
    """
    if len(state2.annotations) != len(state1.annotations):
        return False
    if _check_constraint_merge(state1.constraints, state2.constraints) is False:
        return False
    for v1, v2 in zip(state2.annotations, state1.annotations):
        if type(v1) != type(v2):
            return False
        try:
            if v1.check_merge_annotation(v2) is False:  # type: ignore
                return False
        except AttributeError:
            log.error(
                f"check_merge_annotation() method doesn't exist "
                f"for the annotation {type(v1)}. Aborting merge for the state"
            )
            return False

    return True


def _check_constraint_merge(
    constraints1: Constraints, constraints2: Constraints
) -> bool:
    """
    We are merging the states which have a no more than CONSTRAINT_DIFFERENCE_LIMIT
    different constraints. This helps in merging states which are not too different
    """
    dict1 = {c: True for c in constraints1}
    dict2 = {c: True for c in constraints2}
    c1, c2 = 0, 0
    for key in dict1:
        if key not in dict2 and Not(key) not in dict2:
            c1 += 1
    for key in dict2:
        if key not in dict1 and Not(key) not in dict1:
            c2 += 1
    if c1 + c2 > CONSTRAINT_DIFFERENCE_LIMIT:
        return False
    return True
