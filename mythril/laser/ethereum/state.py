import struct
from z3 import (
    BitVec,
    BitVecVal,
    BitVecRef,
    BitVecSort,
    ExprRef,
    Concat,
    sat,
    simplify,
    Array,
    ForAll,
    Implies,
    UGE,
    UGT,
)
from z3.z3types import Z3Exception
from mythril.disassembler.disassembly import Disassembly
from mythril.laser.ethereum.cfg import Node
from copy import copy, deepcopy
from enum import Enum
from random import randint
from typing import KeysView, Dict, List, Union, Any, Sequence
from mythril.laser.ethereum.util import get_concrete_int

from mythril.laser.ethereum.evm_exceptions import (
    StackOverflowException,
    StackUnderflowException,
)


class CalldataType(Enum):
    CONCRETE = 1
    SYMBOLIC = 2


class Calldata:
    """
    Calldata class representing the calldata of a transaction
    """

    def __init__(self, tx_id, starting_calldata=None):
        """
        Constructor for Calldata
        :param tx_id: unique value representing the transaction the calldata is for
        :param starting_calldata: byte array representing the concrete calldata of a transaction
        """
        self.tx_id = tx_id
        if starting_calldata is not None:
            self._calldata = []
            self.calldatasize = BitVecVal(len(starting_calldata), 256)
            self.concrete = True
        else:
            self._calldata = Array(
                "{}_calldata".format(self.tx_id), BitVecSort(256), BitVecSort(8)
            )
            self.calldatasize = BitVec("{}_calldatasize".format(self.tx_id), 256)
            self.concrete = False

        if self.concrete:
            for calldata_byte in starting_calldata:
                if type(calldata_byte) == int:
                    self._calldata.append(BitVecVal(calldata_byte, 8))
                else:
                    self._calldata.append(calldata_byte)

    def concretized(self, model):
        result = []
        for i in range(
            get_concrete_int(model.eval(self.calldatasize, model_completion=True))
        ):
            result.append(
                get_concrete_int(model.eval(self._calldata[i], model_completion=True))
            )

        return result

    def get_word_at(self, index: int):
        return self[index : index + 32]

    def __getitem__(self, item: Union[int, slice]) -> Any:
        if isinstance(item, slice):
            start, step, stop = item.start, item.step, item.stop
            try:
                if start is None:
                    start = 0
                if step is None:
                    step = 1
                if stop is None:
                    stop = self.calldatasize
                current_index = (
                    start if isinstance(start, BitVecRef) else BitVecVal(start, 256)
                )
                dataparts = []
                while simplify(current_index != stop):
                    dataparts.append(self[current_index])
                    current_index = simplify(current_index + step)
            except Z3Exception:
                raise IndexError("Invalid Calldata Slice")

            values, constraints = zip(*dataparts)
            result_constraints = []
            for c in constraints:
                result_constraints.extend(c)
            return simplify(Concat(values)), result_constraints

        if self.concrete:
            try:
                return self._calldata[get_concrete_int(item)], ()
            except IndexError:
                return BitVecVal(0, 8), ()
        else:
            constraints = [
                Implies(self._calldata[item] != 0, UGT(self.calldatasize, item))
            ]

            return self._calldata[item], constraints


class Storage:
    """
    Storage class represents the storage of an Account
    """

    def __init__(self, concrete=False, address=None, dynamic_loader=None):
        """
        Constructor for Storage
        :param concrete: bool indicating whether to interpret uninitialized storage as concrete versus symbolic
        """
        self._storage = {}
        self.concrete = concrete
        self.dynld = dynamic_loader
        self.address = address

    def __getitem__(self, item: Union[int, slice]) -> Any:
        try:
            return self._storage[item]
        except KeyError:
            if (
                self.address
                and int(self.address[2:], 16) != 0
                and (self.dynld and self.dynld.storage_loading)
            ):
                try:
                    self._storage[item] = int(
                        self.dynld.read_storage(
                            contract_address=self.address, index=int(item)
                        ),
                        16,
                    )
                    return self._storage[item]
                except ValueError:
                    pass
        if self.concrete:
            return 0
        self._storage[item] = BitVec("storage_" + str(item), 256)
        return self._storage[item]

    def __setitem__(self, key: str, value: ExprRef) -> None:
        self._storage[key] = value

    def keys(self) -> KeysView:
        return self._storage.keys()


class Account:
    """
    Account class representing ethereum accounts
    """

    def __init__(
        self,
        address: str,
        code=None,
        contract_name="unknown",
        balance=None,
        concrete_storage=False,
        dynamic_loader=None,
    ):
        """
        Constructor for account
        :param address: Address of the account
        :param code: The contract code of the account
        :param contract_name: The name associated with the account
        :param balance: The balance for the account
        :param concrete_storage: Interpret storage as concrete
        """
        self.nonce = 0
        self.code = code or Disassembly("")
        self.balance = balance if balance else BitVec("balance", 256)
        self.storage = Storage(
            concrete_storage, address=address, dynamic_loader=dynamic_loader
        )

        # Metadata
        self.address = address
        self.contract_name = contract_name

        self.deleted = False

    def __str__(self) -> str:
        return str(self.as_dict)

    def set_balance(self, balance: ExprRef) -> None:
        self.balance = balance

    def add_balance(self, balance: ExprRef) -> None:
        self.balance += balance

    @property
    def as_dict(self) -> Dict:
        return {
            "nonce": self.nonce,
            "code": self.code,
            "balance": self.balance,
            "storage": self.storage,
        }


class Environment:
    """
    The environment class represents the current execution environment for the symbolic executor
    """

    def __init__(
        self,
        active_account: Account,
        sender: ExprRef,
        calldata: Calldata,
        gasprice: ExprRef,
        callvalue: ExprRef,
        origin: ExprRef,
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

    def __str__(self) -> str:
        return str(self.as_dict)

    @property
    def as_dict(self) -> Dict:
        return dict(
            active_account=self.active_account,
            sender=self.sender,
            calldata=self.calldata,
            gasprice=self.gasprice,
            callvalue=self.callvalue,
            origin=self.origin,
            calldata_type=self.calldata_type,
        )


class Constraints(list):
    """
    This class should maintain a solver and it's constraints, This class tries to make the Constraints() object
    as a simple list of constraints with some background processing.
    TODO: add the solver to this class after callback refactor
    """

    def __init__(self, constraint_list=None, solver=None, possibility=None):
        super(Constraints, self).__init__(constraint_list or [])
        self.solver = solver
        self.__possibility = possibility

    def check_possibility(self):
        return True

    def append(self, constraint):
        super(Constraints, self).append(constraint)

    def pop(self, index=-1):
        raise NotImplementedError

    def __copy__(self):
        constraint_list = super(Constraints, self).copy()
        return Constraints(constraint_list)

    def __deepcopy__(self, memodict=None):
        return self.__copy__()

    def __add__(self, constraints):
        constraints_list = super(Constraints, self).__add__(constraints)
        return Constraints(constraint_list=constraints_list)

    def __iadd__(self, constraints):
        super(Constraints, self).__iadd__(constraints)
        return self


class MachineStack(list):
    """
    Defines EVM stack, overrides the default list to handle overflows
    """

    STACK_LIMIT = 1024

    def __init__(self, default_list=None):
        if default_list is None:
            default_list = []
        super(MachineStack, self).__init__(default_list)

    def append(self, element: BitVec) -> None:
        """
        :param element: element to be appended to the list
        :function: appends the element to list if the size is less than STACK_LIMIT, else throws an error
        """
        if super(MachineStack, self).__len__() >= self.STACK_LIMIT:
            raise StackOverflowException(
                "Reached the EVM stack limit of {}, you can't append more "
                "elements".format(self.STACK_LIMIT)
            )
        super(MachineStack, self).append(element)

    def pop(self, index=-1) -> BitVec:
        """
        :param index:index to be popped, same as the list() class.
        :returns popped value
        :function: same as list() class but throws StackUnderflowException for popping from an empty list
        """

        try:
            return super(MachineStack, self).pop(index)
        except IndexError:
            raise StackUnderflowException("Trying to pop from an empty stack")

    def __getitem__(self, item: Union[int, slice]) -> Any:
        try:
            return super(MachineStack, self).__getitem__(item)
        except IndexError:
            raise StackUnderflowException(
                "Trying to access a stack element which doesn't exist"
            )

    def __add__(self, other):
        """
        Implement list concatenation if needed
        """
        raise NotImplementedError("Implement this if needed")

    def __iadd__(self, other):
        """
        Implement list concatenation if needed
        """
        raise NotImplementedError("Implement this if needed")


class MachineState:
    """
    MachineState represents current machine state also referenced to as \mu
    """

    def __init__(
        self, gas: int, pc=0, stack=None, memory=None, constraints=None, depth=0
    ):
        """ Constructor for machineState """
        self.pc = pc
        self.stack = MachineStack(stack)
        self.memory = memory or []
        self.gas = gas
        self.constraints = constraints or Constraints()
        self.depth = depth

    def mem_extend(self, start: int, size: int) -> None:
        """
        Extends the memory of this machine state
        :param start: Start of memory extension
        :param size: Size of memory extension
        """
        if self.memory_size > start + size:
            return
        m_extend = start + size - self.memory_size
        self.memory.extend(bytearray(m_extend))

    def memory_write(self, offset: int, data: List[int]) -> None:
        """ Writes data to memory starting at offset """
        self.mem_extend(offset, len(data))
        self.memory[offset : offset + len(data)] = data

    def pop(self, amount=1) -> Union[BitVec, List[BitVec]]:
        """ Pops amount elements from the stack"""
        if amount >= len(self.stack):
            raise StackUnderflowException
        values = self.stack[-amount:][::-1]
        del self.stack[-amount:]

        return values[0] if amount == 1 else values

    def __deepcopy__(self, memodict=None):
        memodict = {} if memodict is None else memodict
        return MachineState(
            gas=self.gas,
            pc=self.pc,
            stack=copy(self.stack),
            memory=copy(self.memory),
            constraints=copy(self.constraints),
            depth=self.depth,
        )

    def __str__(self):
        return str(self.as_dict)

    @property
    def memory_size(self) -> int:
        return len(self.memory)

    @property
    def as_dict(self) -> Dict:
        return dict(
            pc=self.pc,
            stack=self.stack,
            memory=self.memory,
            memsize=self.memory_size,
            gas=self.gas,
        )


class GlobalState:
    """
    GlobalState represents the current globalstate
    """

    def __init__(
        self,
        world_state: "WorldState",
        environment: Environment,
        node: Node,
        machine_state=None,
        transaction_stack=None,
        last_return_data=None,
    ):
        """ Constructor for GlobalState"""
        self.node = node
        self.world_state = world_state
        self.environment = environment
        self.mstate = machine_state if machine_state else MachineState(gas=10000000)
        self.transaction_stack = transaction_stack if transaction_stack else []
        self.op_code = ""
        self.last_return_data = last_return_data

    def __copy__(self) -> "GlobalState":
        world_state = copy(self.world_state)
        environment = copy(self.environment)
        mstate = deepcopy(self.mstate)
        transaction_stack = copy(self.transaction_stack)
        return GlobalState(
            world_state,
            environment,
            self.node,
            mstate,
            transaction_stack=transaction_stack,
            last_return_data=self.last_return_data,
        )

    @property
    def accounts(self) -> Dict:
        return self.world_state.accounts

    # TODO: remove this, as two instructions are confusing
    def get_current_instruction(self) -> Dict:
        """ Gets the current instruction for this GlobalState"""

        instructions = self.environment.code.instruction_list
        return instructions[self.mstate.pc]

    @property
    def current_transaction(
        self
    ) -> Union["MessageCallTransaction", "ContractCreationTransaction", None]:
        # TODO: Remove circular to transaction package to import Transaction classes
        try:
            return self.transaction_stack[-1][0]
        except IndexError:
            return None

    @property
    def instruction(self) -> Dict:
        return self.get_current_instruction()

    def new_bitvec(self, name: str, size=256) -> BitVec:
        transaction_id = self.current_transaction.id
        return BitVec("{}_{}".format(transaction_id, name), size)


class WorldState:
    """
    The WorldState class represents the world state as described in the yellow paper
    """

    def __init__(self, transaction_sequence=None):
        """
        Constructor for the world state. Initializes the accounts record
        """
        self.accounts = {}
        self.node = None
        self.transaction_sequence = transaction_sequence or []

    def __getitem__(self, item: str) -> Account:
        """
        Gets an account from the worldstate using item as key
        :param item: Address of the account to get
        :return: Account associated with the address
        """
        return self.accounts[item]

    def __copy__(self) -> "WorldState":
        new_world_state = WorldState(transaction_sequence=self.transaction_sequence[:])
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

    def _generate_new_address(self) -> str:
        """ Generates a new address for the global state"""
        while True:
            address = "0x" + "".join([str(hex(randint(0, 16)))[-1] for _ in range(20)])
            if address not in self.accounts.keys():
                return address

    def _put_account(self, account: Account) -> None:
        self.accounts[account.address] = account
