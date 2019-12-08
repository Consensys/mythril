from copy import copy
from typing import Dict, List, Tuple, cast
from mythril.laser.ethereum.svm import LaserEVM
from mythril.laser.ethereum.plugins.plugin import LaserPlugin
from mythril.laser.ethereum.state.world_state import WorldState
from mythril.laser.ethereum.state.account import Account, Storage
from mythril.laser.ethereum.cfg import Node, get_new_gbl_id
from mythril.laser.ethereum.state.constraints import Constraints
from mythril.laser.smt import symbol_factory, Array, If, Or, And, Not, Bool
import logging

log = logging.getLogger(__name__)

CONSTRAINT_DIFFERENCE_LIMIT = 15


class StateMerge(LaserPlugin):
    def initialize(self, symbolic_vm: LaserEVM):
        """Initializes the mutation pruner

        Introduces hooks for SSTORE operations
        :param symbolic_vm:
        :return:
        """

        @symbolic_vm.laser_hook("stop_sym_trans")
        def execute_stop_sym_trans_hook(svm: LaserEVM):
            log.info(svm.open_states)

            open_states = svm.open_states

            if len(open_states) <= 1:
                return
            num_old_states = len(open_states)
            new_states = []  # type: List[WorldState]
            old_size = len(open_states)
            old_states = copy(open_states)
            while old_size != len(new_states):
                old_size = len(new_states)
                new_states = []
                merged_dict = {}  # type: Dict[int, bool]
                for i in range(len(old_states)):
                    if merged_dict.get(i, False):
                        continue
                    i_is_merged = False
                    for j in range(i + 1, len(old_states)):
                        if merged_dict.get(j, False) or not self.check_merge_condition(
                            old_states[i], old_states[j]
                        ):
                            j += 1
                            continue
                        state = old_states[i]
                        self.merge_states(state, old_states[j])
                        merged_dict[j] = True
                        new_states.append(state)
                        i_is_merged = True
                        break

                    if i_is_merged is False:
                        new_states.append(old_states[i])

                old_states = copy(new_states)
            logging.info(
                "States reduced from {} to {}".format(num_old_states, len(new_states))
            )
            svm.open_states = new_states

    def check_merge_condition(self, state1: WorldState, state2: WorldState):
        """
        Check whether two world states can be merged
        :param state1:
        :param state2:
        :return: whether the states can be merged or not
        """
        basic_condition = self.check_ws_merge_condition(state1, state2)
        return basic_condition

    def merge_states(self, state1: WorldState, state2: WorldState):
        """
        Merge state2 into state1
        :param state1: The state to be merged into
        :param state2: The state which is merged into state1
        :return:
        """

        # Merge constraints
        state1.constraints, condition1, _ = self._merge_constraints(
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
                self.merge_accounts(
                    state1._accounts[address], account, condition1, state1.balances
                )

        # Merge annotations
        self._merge_annotations(state1, state2)

        # Merge Node
        self.merge_nodes(state1.node, state2.node, state1.constraints)

    @staticmethod
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

    @staticmethod
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

    def _check_merge_annotations(self, state1: WorldState, state2: WorldState):
        """

        :param state:
        :return:
        """
        if len(state2.annotations) != len(state1._annotations):
            return False
        if (
            self._check_constraint_merge(state1.constraints, state2.constraints)
            is False
        ):
            return False
        for v1, v2 in zip(state2.annotations, state1._annotations):
            if v1.check_merge_annotation(v2) is False:  # type: ignore
                return False
        return True

    @staticmethod
    def _merge_annotations(state1: "WorldState", state2: "WorldState"):
        """

        :param state:
        :return:
        """
        for v1, v2 in zip(state1.annotations, state2.annotations):
            v1.merge_annotations(v2)  # type: ignore

    def check_ws_merge_condition(self, state1: WorldState, state2: WorldState):
        """
        Checks whether we can merge these states or not
        """
        if state1.node and not self.check_node_merge_condition(
            state1.node, state2.node
        ):
            return False

        for address, account in state2.accounts.items():
            if (
                address in state1._accounts
                and self.check_account_merge_condition(
                    state1._accounts[address], account
                )
                is False
            ):
                return False
        if not self._check_merge_annotations(state1, state2):
            return False

        return True

    def merge_accounts(
        self,
        account1: Account,
        account2: Account,
        path_condition: Bool,
        merged_balance: Array,
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
        self.merge_storage(account1.storage, account2.storage, path_condition)

    @staticmethod
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

    @staticmethod
    def check_account_merge_condition(account1: Account, account2: Account):
        """
        Checks whether we can merge accounts or not
        """
        return (
            account1.nonce == account2.nonce
            and account1.deleted == account2.deleted
            and account1.code.bytecode == account2.code.bytecode
        )

    @staticmethod
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

    @staticmethod
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
