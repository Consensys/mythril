from z3 import BitVec, BitVecVal
from copy import copy, deepcopy
from enum import Enum
from random import randint


class CalldataType(Enum):
    CONCRETE = 1
    SYMBOLIC = 2


class Storage:
    """
    Storage class represents the storage of an Account
    """
    def __init__(self, concrete=False):
        """
        Constructor for Storage
        :param concrete: bool indicating whether to interpret uninitialized storage as concrete versus symbolic
        """
        self._storage = {}
        self.concrete = concrete

    def __getitem__(self, item):
        try:
            return self._storage[item]
        except KeyError:
            pass
        if self.concrete:
            return 0
        self._storage[item] = BitVec("storage_" + str(item), 256)
        return self._storage[item]

    def __setitem__(self, key, value):
        self._storage[key] = value


class Account:
    """
    Account class representing ethereum accounts
    """
    def __init__(self, address, code=None, contract_name="unknown", balance=None, concrete_storage=False):
        """
        Constructor for account
        :param address: Address of the account
        :param code: The contract code of the account
        :param contract_name: The name associated with the account
        :param balance: The balance for the account
        :param concrete_storage: Interpret storage as concrete
        """
        self.nonce = 0
        self.code = code
        self.balance = balance if balance else BitVec("balance", 256)
        self.storage = Storage(concrete_storage)

        # Metadata
        self.address = address
        self.contract_name = contract_name

    def __str__(self):
        return str(self.as_dict)

    def set_balance(self, balance):
        self.balance = balance

    def add_balance(self, balance):
        self.balance += balance

    @property
    def as_dict(self):
        return {'nonce': self.nonce, 'code': self.code, 'balance': self.balance, 'storage': self.storage}


class Environment:
    """
    The environment class represents the current execution environment for the symbolic executor
    """
    def __init__(
        self,
        active_account,
        sender,
        calldata,
        gasprice,
        callvalue,
        origin,
        code=None,
        calldata_type=CalldataType.SYMBOLIC,
    ):
        # Metadata

        self.active_account = active_account
        self.active_function_name = ""

        self.address = BitVecVal(int(active_account.address, 16), 256)

        # Ib
        self.code = active_account.code if code is None else code

        self.sender = sender
        self.calldata = calldata
        self.calldata_type = calldata_type
        self.gasprice = gasprice
        self.origin = origin
        self.callvalue = callvalue

    def __str__(self):
        return str(self.as_dict)


    @property
    def as_dict(self):
        return dict(active_account=self.active_account, sender=self.sender, calldata=self.calldata,
                    gasprice=self.gasprice, callvalue=self.callvalue, origin=self.origin,
                    calldata_type=self.calldata_type)


class MachineState:
    """
    MachineState represents current machine state also referenced to as \mu
    """
    def __init__(self, gas):
        """ Constructor for machineState """
        self.pc = 0
        self.stack = []
        self.memory = []
        self.gas = gas
        self.constraints = []
        self.depth = 0

    def mem_extend(self, start, size):
        """
        Extends the memory of this machine state
        :param start: Start of memory extension
        :param size: Size of memory extension
        """
        self.memory += [0] * max(0, start + size - self.memory_size)

    def memory_write(self, offset, data):
        """ Writes data to memory starting at offset """
        self.mem_extend(offset, len(data))
        for memory_index, data_index in zip(
            range(offset, offset + len(data)),
            range(len(data))
        ):
            self.memory[memory_index] = data[data_index]

    def pop(self, amount=1):
        """ Pops amount elements from the stack"""
        if amount >= len(self.stack):
            raise IndexError()
        values = self.stack[-amount:][::-1]
        del self.stack[-amount:]

        return values[0] if amount == 1 else values

    def __str__(self):
        return str(self.as_dict)

    @property
    def memory_size(self):
        return len(self.memory)

    @property
    def as_dict(self):
        return dict(pc=self.pc, stack=self.stack, memory=self.memory, memsize=self.memory_size, gas=self.gas)


class GlobalState:
    """
    GlobalState represents the current globalstate
    """
    def __init__(self, world_state, environment, node, machine_state=None, transaction_stack=None, last_return_data=None):
        """ Constructor for GlobalState"""
        self.node = node
        self.world_state = world_state
        self.environment = environment
        self.mstate = machine_state if machine_state else MachineState(gas=10000000)
        self.transaction_stack = transaction_stack if transaction_stack else []
        self.op_code = ""
        self.last_return_data = last_return_data

    def __copy__(self):
        world_state = copy(self.world_state)
        environment = copy(self.environment)
        mstate = deepcopy(self.mstate)
        transaction_stack = copy(self.transaction_stack)
        return GlobalState(world_state, environment, self.node, mstate, transaction_stack=transaction_stack,
                           last_return_data=self.last_return_data)

    @property
    def accounts(self):
        return self.world_state.accounts

    # TODO: remove this, as two instructions are confusing
    def get_current_instruction(self):
        """ Gets the current instruction for this GlobalState"""


        instructions = self.environment.code.instruction_list
        return instructions[self.mstate.pc]

    @property
    def current_transaction(self):
        try:
            return self.transaction_stack[-1][0]
        except IndexError:
            return None


class WorldState:
    """
    The WorldState class represents the world state as described in the yellow paper
    """
    def __init__(self):
        """
        Constructor for the world state. Initializes the accounts record
        """
        self.accounts = {}
        self.node = None

    def __getitem__(self, item):
        """
        Gets an account from the worldstate using item as key
        :param item: Address of the account to get
        :return: Account associated with the address
        """
        return self.accounts[item]

    def __copy__(self):
        new_world_state = WorldState()
        new_world_state.accounts = copy(self.accounts)
        new_world_state.node = self.node
        return new_world_state

    def create_account(self, balance=0, address=None, concrete_storage=False):
        """
        Create non-contract account
        :param address: The account's address
        :param balance: Initial balance for the account
        :param concrete_storage: Interpret account storage as concrete
        :return: The new account
        """
        address = address if address else self._generate_new_address()
        new_account = Account(address, balance=balance, concrete_storage=concrete_storage)
        self._put_account(new_account)
        return new_account

    def create_initialized_contract_account(self, contract_code, storage):
        """
        Creates a new contract account, based on the contract code and storage provided
        The contract code only includes the runtime contract bytecode
        :param contract_code: Runtime bytecode for the contract
        :param storage: Initial storage for the contract
        :return: The new account
        """
        new_account = Account(self._generate_new_address(), code=contract_code, balance=0)
        new_account.storage = storage
        self._put_account(new_account)

    def _generate_new_address(self):
        """ Generates a new address for the global state"""
        while True:
            address = '0x' + ''.join([str(hex(randint(0, 16)))[-1] for _ in range(20)])
            if address not in self.accounts.keys():
                return address

    def _put_account(self, account):
        self.accounts[account.address] = account
