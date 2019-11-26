"""This module contains a representation of the EVM's world state."""
from copy import copy
from random import randint
from typing import Dict, List, Iterator, Optional, Tuple, TYPE_CHECKING, cast

from mythril.support.loader import DynLoader
from mythril.laser.smt import symbol_factory, Array, BitVec, If, Or, And, Not, Bool
from ethereum.utils import mk_contract_address
from mythril.laser.ethereum.state.account import Account
from mythril.laser.ethereum.state.annotation import StateAnnotation
from mythril.laser.ethereum.state.constraints import Constraints

if TYPE_CHECKING:
    from mythril.laser.ethereum.cfg import Node

CONSTRAINT_DIFFERENCE_LIMIT = 15


class WorldState:
    """The WorldState class represents the world state as described in the
    yellow paper."""

    def __init__(
        self,
        transaction_sequence=None,
        annotations: List[StateAnnotation] = None,
        constraints: Constraints = None,
    ) -> None:
        """Constructor for the world state. Initializes the accounts record.

        :param transaction_sequence:
        :param annotations:
        """
        self._accounts = {}  # type: Dict[int, Account]
        self.balances = Array("balance", 256, 256)  # type: Array
        self.starting_balances = copy(self.balances)
        self.constraints = constraints or Constraints()

        self.node = None  # type: Optional['Node']
        self.transaction_sequence = transaction_sequence or []
        self._annotations = annotations or []

    def merge_states(self, state: "WorldState"):
        """
        Merge this state with "state"
        :param state: The state to be merged with
        :return:
        """

        # Merge constraints
        self.constraints, condition1, _ = self._merge_constraints(state.constraints)

        # Merge balances
        self.balances = cast(Array, If(condition1, self.balances, state.balances))
        self.starting_balances = cast(
            Array, If(condition1, self.starting_balances, state.starting_balances)
        )

        # Merge accounts
        for address, account in state.accounts.items():
            if address not in self._accounts:
                self.put_account(account)
            else:
                self._accounts[address].merge_accounts(
                    account, condition1, self.balances
                )

        # Merge annotations
        self._merge_annotations(state)

        # Merge Node
        self.node.merge_nodes(state.node, self.constraints)

    def _merge_constraints(
        self, constraints: Constraints
    ) -> Tuple[Constraints, Bool, Bool]:
        dict1, dict2 = {}, {}
        for constraint in self.constraints:
            dict1[constraint] = True
        for constraint in constraints:
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

    def _check_constraint_merge(self, constraints: Constraints) -> bool:
        dict1, dict2 = {}, {}
        for constraint in self.constraints:
            dict1[constraint] = True
        for constraint in constraints:
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

    def _check_merge_annotations(self, state: "WorldState"):
        """

        :param state:
        :return:
        """
        if len(state.annotations) != len(self._annotations):
            return False
        if self._check_constraint_merge(state.constraints) is False:
            return False
        for v1, v2 in zip(state.annotations, self._annotations):
            if v1.check_merge_annotation(v2) is False:  # type: ignore
                return False
        return True

    def _merge_annotations(self, state: "WorldState"):
        """

        :param state:
        :return:
        """
        for v1, v2 in zip(state.annotations, self._annotations):
            v1.merge_annotations(v2)  # type: ignore

    def check_merge_condition(self, state: "WorldState"):
        """
        Checks whether we can merge this state with "state" or not
        :param state: The state to check the merge-ability with
        :return: True if we can merge them
        """
        if self.node and not self.node.check_merge_condition(state.node):
            return False

        for address, account in state.accounts.items():
            if (
                address in self._accounts
                and self._accounts[address].check_merge_condition(account) is False
            ):
                return False
        if not self._check_merge_annotations(state):
            return False

        return True

    @property
    def accounts(self):
        return self._accounts

    def __getitem__(self, item: BitVec) -> Account:
        """Gets an account from the worldstate using item as key.

        :param item: Address of the account to get
        :return: Account associated with the address
        """
        try:
            return self._accounts[item.value]
        except KeyError:
            new_account = Account(address=item, code=None, balances=self.balances)
            self._accounts[item.value] = new_account
            return new_account

    def __copy__(self) -> "WorldState":
        """

        :return:
        """
        new_annotations = [copy(a) for a in self._annotations]
        new_world_state = WorldState(
            transaction_sequence=self.transaction_sequence[:],
            annotations=new_annotations,
        )
        new_world_state.balances = copy(self.balances)
        new_world_state.starting_balances = copy(self.starting_balances)
        for account in self._accounts.values():
            new_world_state.put_account(copy(account))
        new_world_state.node = self.node
        new_world_state.constraints = copy(self.constraints)
        return new_world_state

    def accounts_exist_or_load(self, addr: str, dynamic_loader: DynLoader) -> str:
        """
        returns account if it exists, else it loads from the dynamic loader
        :param addr: address
        :param dynamic_loader: Dynamic Loader
        :return: The code
        """
        addr_bitvec = symbol_factory.BitVecVal(int(addr, 16), 256)
        if addr_bitvec.value in self.accounts:
            code = self.accounts[addr_bitvec.value].code
        else:
            code = dynamic_loader.dynld(addr)
            self.create_account(
                balance=0, address=addr_bitvec.value, dynamic_loader=dynamic_loader
            )
        if code is None:
            code = ""
        else:
            code = code.bytecode
        return code

    def create_account(
        self,
        balance=0,
        address=None,
        concrete_storage=False,
        dynamic_loader=None,
        creator=None,
    ) -> Account:
        """Create non-contract account.

        :param address: The account's address
        :param balance: Initial balance for the account
        :param concrete_storage: Interpret account storage as concrete
        :param dynamic_loader: used for dynamically loading storage from the block chain
        :return: The new account
        """
        address = (
            symbol_factory.BitVecVal(address, 256)
            if address
            else self._generate_new_address(creator)
        )

        new_account = Account(
            address=address,
            balances=self.balances,
            dynamic_loader=dynamic_loader,
            concrete_storage=concrete_storage,
        )
        if balance:
            new_account.add_balance(symbol_factory.BitVecVal(balance, 256))

        self.put_account(new_account)
        return new_account

    def create_initialized_contract_account(self, contract_code, storage) -> None:
        """Creates a new contract account, based on the contract code and
        storage provided The contract code only includes the runtime contract
        bytecode.

        :param contract_code: Runtime bytecode for the contract
        :param storage: Initial storage for the contract
        :return: The new account
        """
        # TODO: Add type hints
        new_account = Account(
            self._generate_new_address(), code=contract_code, balances=self.balances
        )
        new_account.storage = storage
        self.put_account(new_account)

    def annotate(self, annotation: StateAnnotation) -> None:
        """

        :param annotation:
        """
        self._annotations.append(annotation)

    @property
    def annotations(self) -> List[StateAnnotation]:
        """

        :return:
        """
        return self._annotations

    def get_annotations(self, annotation_type: type) -> Iterator[StateAnnotation]:
        """Filters annotations for the queried annotation type. Designed
        particularly for modules with annotations:
        worldstate.get_annotations(MySpecificModuleAnnotation)

        :param annotation_type: The type to filter annotations for
        :return: filter of matching annotations
        """
        return filter(lambda x: isinstance(x, annotation_type), self.annotations)

    def _generate_new_address(self, creator=None) -> BitVec:
        """Generates a new address for the global state.

        :return:
        """
        if creator:
            # TODO: Use nounce
            address = "0x" + str(mk_contract_address(creator, 0).hex())
            return symbol_factory.BitVecVal(int(address, 16), 256)
        while True:
            address = "0x" + "".join([str(hex(randint(0, 16)))[-1] for _ in range(40)])
            if address not in self._accounts.keys():
                return symbol_factory.BitVecVal(int(address, 16), 256)

    def put_account(self, account: Account) -> None:
        """

        :param account:
        """
        self._accounts[account.address.value] = account
        account._balances = self.balances
