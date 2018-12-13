from copy import copy
from random import randint
from typing import List

from mythril.laser.ethereum.state.account import Account
from mythril.laser.ethereum.state.annotation import StateAnnotation


class WorldState:
    """
    The WorldState class represents the world state as described in the yellow paper
    """

    def __init__(
        self, transaction_sequence=None, annotations: List[StateAnnotation] = None
    ) -> None:
        """
        Constructor for the world state. Initializes the accounts record
        """
        self.accounts = {}
        self.node = None
        self.transaction_sequence = transaction_sequence or []
        self._annotations = annotations or []

    def __getitem__(self, item: str) -> Account:
        """
        Gets an account from the worldstate using item as key
        :param item: Address of the account to get
        :return: Account associated with the address
        """
        return self.accounts[item]

    def __copy__(self) -> "WorldState":
        new_annotations = [copy(a) for a in self._annotations]
        new_world_state = WorldState(
            transaction_sequence=self.transaction_sequence[:],
            annotations=new_annotations,
        )
        new_world_state.accounts = copy(self.accounts)
        new_world_state.node = self.node
        return new_world_state

    def create_account(
        self, balance=0, address=None, concrete_storage=False, dynamic_loader=None
    ) -> Account:
        """
        Create non-contract account
        :param address: The account's address
        :param balance: Initial balance for the account
        :param concrete_storage: Interpret account storage as concrete
        :param dynamic_loader: used for dynamically loading storage from the block chain
        :return: The new account
        """
        address = address if address else self._generate_new_address()
        new_account = Account(
            address,
            balance=balance,
            dynamic_loader=dynamic_loader,
            concrete_storage=concrete_storage,
        )
        self._put_account(new_account)
        return new_account

    def create_initialized_contract_account(self, contract_code, storage) -> None:
        """
        Creates a new contract account, based on the contract code and storage provided
        The contract code only includes the runtime contract bytecode
        :param contract_code: Runtime bytecode for the contract
        :param storage: Initial storage for the contract
        :return: The new account
        """
        # TODO: Add type hints
        new_account = Account(
            self._generate_new_address(), code=contract_code, balance=0
        )
        new_account.storage = storage
        self._put_account(new_account)

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

    def _generate_new_address(self) -> str:
        """ Generates a new address for the global state"""
        while True:
            address = "0x" + "".join([str(hex(randint(0, 16)))[-1] for _ in range(20)])
            if address not in self.accounts.keys():
                return address

    def _put_account(self, account: Account) -> None:
        self.accounts[account.address] = account
