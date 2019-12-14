from mythril.laser.ethereum.cfg import Node
from mythril.laser.ethereum.state.world_state import WorldState
from mythril.laser.ethereum.state.account import Account
from mythril.laser.ethereum.state.constraints import Constraints
from mythril.laser.smt import Not

CONSTRAINT_DIFFERENCE_LIMIT = 15


def check_node_merge_condition(node1: Node, node2: Node):
    """
    Checks whether two nodes are merge-able or not
    :param node1: The node to be merged
    :param node2: The other node to be merged
    :return: Boolean, True if we can merge
    """
    return (
        node1.function_name == node2.function_name
        and node1.contract_name == node2.contract_name
        and node1.start_addr == node2.start_addr
    )


def check_account_merge_condition(account1: Account, account2: Account):
    """
    Checks whether we can merge accounts or not
    """
    return (
        account1.nonce == account2.nonce
        and account1.deleted == account2.deleted
        and account1.code.bytecode == account2.code.bytecode
    )


def check_ws_merge_condition(state1: WorldState, state2: WorldState):
    """
    Checks whether we can merge these states or not
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

    :param state:
    :return:
    """
    if len(state2.annotations) != len(state1._annotations):
        return False
    if _check_constraint_merge(state1.constraints, state2.constraints) is False:
        return False
    for v1, v2 in zip(state2.annotations, state1._annotations):
        if v1.check_merge_annotation(v2) is False:  # type: ignore
            return False
    return True


def _check_constraint_merge(
    constraints1: Constraints, constraints2: Constraints
) -> bool:
    dict1, dict2 = {}, {}
    for constraint in constraints1:
        dict1[constraint] = True
    for constraint in constraints2:
        dict2[constraint] = True
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
