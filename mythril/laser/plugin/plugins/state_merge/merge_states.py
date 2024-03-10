import logging

from mythril.laser.ethereum.cfg import Node
from typing import Tuple, cast
from mythril.laser.ethereum.state.world_state import WorldState
from mythril.laser.ethereum.state.account import Account, Storage
from mythril.laser.ethereum.state.constraints import Constraints
from mythril.laser.smt import symbol_factory, Array, If, Or, And, Not, Bool

log = logging.getLogger(__name__)


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
    Merges node2 into node1
    :param node1: The node to be merged
    :param node2: The other node to be merged
    :param constraints: The merged constraints
    :return:
    """
    node1.states += node2.states
    node1.uid = hash(node1)
    node1.flags |= node2.flags
    node1.constraints = constraints


def merge_accounts(
    account1: Account,
    account2: Account,
    path_condition: Bool,
    merged_balance: Array,
):
    """
    Merges account2 into account1
    :param account1: The account to merge with
    :param account2: The second account to merge
    :param path_condition: The constraint for this account
    :param merged_balance: The merged balance
    :return:
    """
    if (
        account1.nonce != account2.nonce
        or account1.deleted != account2.deleted
        or account1.code.bytecode != account2.code.bytecode
    ):
        raise ValueError("Un-Mergeable accounts are given to be merged")

    account1._balances = merged_balance
    merge_storage(account1.storage, account2.storage, path_condition)


def merge_storage(storage1: Storage, storage2: Storage, path_condition: Bool):
    """
    Merge storage2 into storage1
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
            storage1.printable_storage[key] = If(path_condition, 0, value)


def _merge_annotations(state1: "WorldState", state2: "WorldState"):
    """
    Merges the annotations of the two states into state1
    :param state1:
    :param state2:
    :return:
    """
    for v1, v2 in zip(state1.annotations, state2.annotations):
        try:
            v1.merge_annotation(v2)  # type: ignore
        except AttributeError:
            log.error(
                f"merge_annotation() method doesn't exist for the annotation {type(v1)}. "
                "Aborting merge for the state"
            )
            return False


def _merge_constraints(
    constraints1: Constraints, constraints2: Constraints
) -> Tuple[Constraints, Bool, Bool]:
    """
    Merges constraints
    :param constraints1: Constraint2 of state1
    :param constraints2: Constraints of state2
    :return: A Tuple of merged constraints,
    conjunction of constraints in state 1 not in state 2, conjunction of constraints
    in state2 not in state1
    """
    dict1 = {c: True for c in constraints1}
    dict2 = {c: True for c in constraints2}
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
