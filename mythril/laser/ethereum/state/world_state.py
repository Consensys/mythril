"""This module contains a representation of the EVM's world state."""
from copy import copy, deepcopy
from random import randint
from typing import Dict, List, Iterator, Optional, TYPE_CHECKING
from eth._utils.address import generate_contract_address

from mythril.support.loader import DynLoader
from mythril.laser.smt import symbol_factory, Array, BitVec
from mythril.laser.ethereum.state.account import Account
from mythril.laser.ethereum.state.annotation import StateAnnotation
from mythril.laser.ethereum.state.constraints import Constraints

if TYPE_CHECKING:
    from mythril.laser.ethereum.cfg import Node


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
        self.balances = Array("balance", 256, 256)
        self.starting_balances = deepcopy(self.balances)
        self.constraints = constraints or Constraints()

        self.node = None  # type: Optional['Node']
        self.transaction_sequence = transaction_sequence or []
        self._annotations = annotations or []

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

    def __deepcopy__(self, _) -> "WorldState":
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
        new_world_state.constraints = deepcopy(self.constraints)
        return new_world_state

    def accounts_exist_or_load(self, addr, dynamic_loader: DynLoader) -> Account:
        """
        returns account if it exists, else it loads from the dynamic loader
        :param addr: address
        :param dynamic_loader: Dynamic Loader
        :return: The code
        """

        if isinstance(addr, str):
            addr = int(addr, 16)

        if isinstance(addr, int):
            addr_bitvec = symbol_factory.BitVecVal(addr, 256)
        elif not isinstance(addr, BitVec):
            addr_bitvec = symbol_factory.BitVecVal(int(addr, 16), 256)
        else:
            addr_bitvec = addr

        if addr_bitvec.value in self.accounts:
            return self.accounts[addr_bitvec.value]
        if dynamic_loader is None:
            raise ValueError("dynamic_loader is None")

        if isinstance(addr, int):
            try:
                balance = dynamic_loader.read_balance("{0:#0{1}x}".format(addr, 42))
                return self.create_account(
                    balance=balance,
                    address=addr_bitvec.value,
                    dynamic_loader=dynamic_loader,
                    code=dynamic_loader.dynld(addr),
                    concrete_storage=True,
                )
            except ValueError:
                # Initial balance will be a symbolic variable
                pass
        try:
            code = dynamic_loader.dynld(addr)
        except ValueError:
            code = None
        return self.create_account(
            address=addr_bitvec.value, dynamic_loader=dynamic_loader, code=code
        )

    def create_account(
        self,
        balance=0,
        address=None,
        concrete_storage=False,
        dynamic_loader=None,
        creator=None,
        code=None,
        nonce=0,
    ) -> Account:
        """Create non-contract account.

        :param address: The account's address
        :param balance: Initial balance for the account
        :param concrete_storage: Interpret account storage as concrete
        :param dynamic_loader: used for dynamically loading storage from the block chain
        :param creator: The address of the creator of the contract if it's a contract
        :param code: The code of the contract, if it's a contract
        :param nonce: Nonce of the account
        :return: The new account
        """
        if creator in self.accounts:
            nonce = self.accounts[creator].nonce
        elif creator:
            self.create_account(address=creator)

        address = (
            symbol_factory.BitVecVal(address, 256)
            if address is not None
            else self._generate_new_address(creator, nonce=self.accounts[creator].nonce)
        )
        if creator:
            self.accounts[creator].nonce += 1
        new_account = Account(
            address=address,
            balances=self.balances,
            dynamic_loader=dynamic_loader,
            concrete_storage=concrete_storage,
        )
        if code:
            new_account.code = code
        new_account.nonce = nonce
        new_account.set_balance(symbol_factory.BitVecVal(balance, 256))

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

    def _generate_new_address(self, creator=None, nonce=0) -> BitVec:
        """Generates a new address for the global state.

        :return:
        """
        if creator:
            # TODO: Use nounce
            address = "0x" + str(generate_contract_address(creator, nonce).hex())
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
