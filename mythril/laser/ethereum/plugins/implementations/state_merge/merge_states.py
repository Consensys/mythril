from mythril.laser.ethereum.cfg import Node, get_new_gbl_id
from typing import Tuple, cast
from mythril.laser.ethereum.state.world_state import WorldState
from mythril.laser.ethereum.state.account import Account, Storage
from mythril.laser.ethereum.state.constraints import Constraints
from mythril.laser.smt import symbol_factory, Array, If, Or, And, Not, Bool


def merge_states(state1: WorldState, state2: WorldState):
    """
    Merge state2 into state1
    :param state1: The state to be merged into
    :param state2: The state which is merged into state1
    :return:
    """

    # Merge constraints
    state1.constraints, condition1, _ = _merge_constraints(
        state1.constraints, state2.constraints
    )

    # Merge balances
    state1.balances = cast(Array, If(condition1, state1.balances, state2.balances))
    state1.starting_balances = cast(
        Array, If(condition1, state1.starting_balances, state2.starting_balances)
    )

    # Merge accounts
    for address, account in state2.accounts.items():
        if address not in state1._accounts:
            state1.put_account(account)
        else:
            merge_accounts(
                state1._accounts[address], account, condition1, state1.balances
            )

    # Merge annotations
    _merge_annotations(state1, state2)

    # Merge Node
    merge_nodes(state1.node, state2.node, state1.constraints)


def merge_nodes(node1: Node, node2: Node, constraints: Constraints):
    """
    Merges two nodes
    :param node1: The node to be merged
    :param node2: The other node to be merged
    :param constraints: The merged constraints
    :return:
    """
    node1.states += node2.states
    node1.uid = get_new_gbl_id()
    node1.flags |= node2.flags
    node1.constraints = constraints


def merge_accounts(
    account1: Account, account2: Account, path_condition: Bool, merged_balance: Array,
):
    """
    Checks the merge-ability
    :param account1: The account to merge with
    :param account2: The second account to merge
    :param path_condition: The constraint for this account
    :param merged_balance: The merged balance
    :return:
    """
    assert (
        account1.nonce == account2.nonce
        and account1.deleted == account2.deleted
        and account1.code.bytecode == account2.code.bytecode
    )

    account1._balances = merged_balance
    account1.balance = lambda: account1._balances[account1.address]
    merge_storage(account1.storage, account2.storage, path_condition)


def merge_storage(storage1: Storage, storage2: Storage, path_condition: Bool):
    """
    Merge storage
    :param storage1: To storage to merge into
    :param storage2: To storage to merge with
    :param path_condition: The constraint for this storage to be executed
    :return:
    """
    storage1._standard_storage = If(
        path_condition, storage1._standard_storage, storage2._standard_storage
    )
    storage1.storage_keys_loaded = storage1.storage_keys_loaded.union(
        storage2.storage_keys_loaded
    )
    for key, value in storage2.printable_storage.items():
        if key in storage1.printable_storage:
            storage1.printable_storage[key] = If(
                path_condition, storage1.printable_storage[key], value
            )
        else:
            storage1.printable_storage[key] = value


def _merge_annotations(state1: "WorldState", state2: "WorldState"):
    """

    :param state:
    :return:
    """
    for v1, v2 in zip(state1.annotations, state2.annotations):
        v1.merge_annotations(v2)  # type: ignore


def _merge_constraints(
    constraints1: Constraints, constraints2: Constraints
) -> Tuple[Constraints, Bool, Bool]:
    dict1, dict2 = {}, {}
    for constraint in constraints1:
        dict1[constraint] = True
    for constraint in constraints2:
        dict2[constraint] = True
    c1, c2 = symbol_factory.Bool(True), symbol_factory.Bool(True)
    new_constraint1, new_constraint2 = (
        symbol_factory.Bool(True),
        symbol_factory.Bool(True),
    )
    same_constraints = Constraints()
    for key in dict1:
        if key not in dict2:
            c1 = And(c1, key)
            if Not(key) not in dict2:
                new_constraint1 = And(new_constraint1, key)
        else:
            same_constraints.append(key)
    for key in dict2:
        if key not in dict1:
            c2 = And(c2, key)
            if Not(key) not in dict1:
                new_constraint2 = And(new_constraint2, key)
        else:
            same_constraints.append(key)
    merge_constraints = same_constraints + [Or(new_constraint1, new_constraint2)]
    return merge_constraints, c1, c2
