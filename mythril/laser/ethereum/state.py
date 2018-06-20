from z3 import BitVec, BitVecVal
from copy import copy, deepcopy
from enum import Enum


class CalldataType(Enum):
    CONCRETE = 1
    SYMBOLIC = 2

class Account:
    """
    Account class representing ethereum accounts
    """
    def __init__(self, address, code=None, contract_name="unknown", balance=None):
        """
        Constructor for account
        :param address: Address of the account
        :param code: The contract code of the account
        :param contract_name: The name associated with the account
        :param balance: The balance for the account
        """
        self.nonce = 0
        self.code = code
        self.balance = balance if balance else BitVec("balance", 256)
        self.storage = {}

        # Metadata
        self.address = address
        self.contract_name = contract_name

    def __str__(self):
        return str(self.as_dict)

    def get_storage(self, index):
        return self.storage[index] if index in self.storage.keys() else BitVec("storage_" + str(index), 256)

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
        calldata_type=CalldataType.SYMBOLIC,
    ):
        # Metadata

        self.active_account = active_account
        self.active_function_name = ""

        self.address = BitVecVal(int(active_account.address, 16), 256)
        self.code = active_account.code

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
        self.memory_size = 0
        self.gas = gas
        self.constraints = []
        self.depth = 0

    def mem_extend(self, start, size):
        """
        Extends the memory of this machine state
        :param start: Start of memory extension
        :param size: Size of memory extension
        """
        if start < 4096 and size < 4096:

            if size and start + size > len(self.memory):
                n_append = start + size - len(self.memory)

                while n_append > 0:
                    self.memory.append(0)
                    n_append -= 1

                # FIXME: this does not seem right
                self.memory_size = size

        else:
            # TODO: Specific exception
            raise Exception
            # TODO: Deduct gas for memory extension... not yet implemented

    def __str__(self):
        return str(self.as_dict)

    @property
    def as_dict(self):
        return dict(pc=self.pc, stack=self.stack, memory=self.memory, memsize=self.memory_size, gas=self.gas)


class GlobalState:
    """
    GlobalState represents the current globalstate
    """
    def __init__(self, accounts, environment, node, machine_state=None, call_stack=None):
        """ Constructor for GlobalState"""
        self.node = node
        self.accounts = accounts
        self.environment = environment
        self.mstate = machine_state if machine_state else MachineState(gas=10000000)
        self.call_stack = call_stack if call_stack else []

    def __copy__(self):
        accounts = copy(self.accounts)
        environment = copy(self.environment)
        mstate = deepcopy(self.mstate)
        return GlobalState(accounts, environment, self.node, mstate)

    #TODO: remove this, as two instructions are confusing
    def get_current_instruction(self):
        """ Gets the current instruction for this GlobalState"""
        instructions = self.environment.code.instruction_list
        return instructions[self.mstate.pc]
