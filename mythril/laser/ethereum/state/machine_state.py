"""This module contains a representation of the EVM's machine state and its
stack."""
from copy import copy
from typing import cast, Sized, Union, Any, List, Dict, Optional

from mythril.laser.smt import BitVec, Expression

from ethereum import opcodes, utils
from mythril.laser.ethereum.evm_exceptions import (
    StackOverflowException,
    StackUnderflowException,
    OutOfGasException,
)
from mythril.laser.ethereum.state.constraints import Constraints
from mythril.laser.ethereum.state.memory import Memory


class MachineStack(list):
    """Defines EVM stack, overrides the default list to handle overflows."""

    STACK_LIMIT = 1024

    def __init__(self, default_list=None) -> None:
        """

        :param default_list:
        """
        if default_list is None:
            default_list = []
        super(MachineStack, self).__init__(default_list)

    def append(self, element: Expression) -> None:
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

    def pop(self, index=-1) -> Expression:
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
        """

        :param item:
        :return:
        """
        try:
            return super(MachineStack, self).__getitem__(item)
        except IndexError:
            raise StackUnderflowException(
                "Trying to access a stack element which doesn't exist"
            )

    def __add__(self, other):
        """Implement list concatenation if needed.

        :param other:
        """
        raise NotImplementedError("Implement this if needed")

    def __iadd__(self, other):
        """Implement list concatenation if needed.

        :param other:
        """
        raise NotImplementedError("Implement this if needed")


class MachineState:
    """MachineState represents current machine state also referenced to as \mu.
    """

    def __init__(
        self,
        gas_limit: int,
        pc=0,
        stack=None,
        memory: Optional[Memory] = None,
        constraints=None,
        depth=0,
        max_gas_used=0,
        min_gas_used=0,
    ) -> None:
        """Constructor for machineState.

        :param gas_limit:
        :param pc:
        :param stack:
        :param memory:
        :param constraints:
        :param depth:
        :param max_gas_used:
        :param min_gas_used:
        """
        self.pc = pc
        self.stack = MachineStack(stack)
        self.memory = memory or Memory()
        self.gas_limit = gas_limit
        self.min_gas_used = min_gas_used  # lower gas usage bound
        self.max_gas_used = max_gas_used  # upper gas usage bound
        self.constraints = constraints or Constraints()
        self.depth = depth

    def calculate_extension_size(self, start: int, size: int) -> int:
        """

        :param start:
        :param size:
        :return:
        """
        if self.memory_size > start + size:
            return 0
        return start + size - self.memory_size

    def calculate_memory_gas(self, start: int, size: int):
        """

        :param start:
        :param size:
        :return:
        """
        # https://github.com/ethereum/pyethereum/blob/develop/ethereum/vm.py#L148
        oldsize = self.memory_size // 32
        old_totalfee = (
            oldsize * opcodes.GMEMORY + oldsize ** 2 // opcodes.GQUADRATICMEMDENOM
        )
        newsize = utils.ceil32(start + size) // 32
        new_totalfee = (
            newsize * opcodes.GMEMORY + newsize ** 2 // opcodes.GQUADRATICMEMDENOM
        )
        return new_totalfee - old_totalfee

    def check_gas(self):
        """Check whether the machine is out of gas."""
        if self.min_gas_used > self.gas_limit:
            raise OutOfGasException()

    def mem_extend(self, start: int, size: int) -> None:
        """Extends the memory of this machine state.

        :param start: Start of memory extension
        :param size: Size of memory extension
        """
        m_extend = self.calculate_extension_size(start, size)
        if m_extend:
            extend_gas = self.calculate_memory_gas(start, size)
            self.min_gas_used += extend_gas
            self.max_gas_used += extend_gas
            self.check_gas()
            self.memory.extend(m_extend)

    def memory_write(self, offset: int, data: List[Union[int, BitVec]]) -> None:
        """Writes data to memory starting at offset.

        :param offset:
        :param data:
        """
        self.mem_extend(offset, len(data))
        self.memory[offset : offset + len(data)] = data

    def pop(self, amount=1) -> Union[BitVec, List[BitVec]]:
        """Pops amount elements from the stack.

        :param amount:
        :return:
        """
        if amount > len(self.stack):
            raise StackUnderflowException
        values = self.stack[-amount:][::-1]
        del self.stack[-amount:]

        return values[0] if amount == 1 else values

    def __deepcopy__(self, memodict=None):
        """

        :param memodict:
        :return:
        """
        memodict = {} if memodict is None else memodict
        return MachineState(
            gas_limit=self.gas_limit,
            max_gas_used=self.max_gas_used,
            min_gas_used=self.min_gas_used,
            pc=self.pc,
            stack=copy(self.stack),
            memory=copy(self.memory),
            constraints=copy(self.constraints),
            depth=self.depth,
        )

    def __str__(self):
        """

        :return:
        """
        return str(self.as_dict)

    @property
    def memory_size(self) -> int:
        """

        :return:
        """
        return len(cast(Sized, self.memory))

    @property
    def as_dict(self) -> Dict:
        """

        :return:
        """
        return dict(
            pc=self.pc,
            stack=self.stack,
            memory=self.memory,
            memsize=self.memory_size,
            gas=self.gas_limit,
            max_gas_used=self.max_gas_used,
            min_gas_used=self.min_gas_used,
        )
