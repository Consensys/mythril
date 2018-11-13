from copy import copy
from typing import Union, Any, List, Dict

from z3 import BitVec

from mythril.laser.ethereum.evm_exceptions import (
    StackOverflowException,
    StackUnderflowException,
)
from mythril.laser.ethereum.state.constraints import Constraints


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
        if amount > len(self.stack):
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
