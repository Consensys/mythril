import pytest

from mythril.laser.ethereum.state import MachineStack
from mythril.laser.ethereum.evm_exceptions import *
from tests import BaseTestCase


class MachineStackTest(BaseTestCase):

    @staticmethod
    def test_mstack_constructor():
        mstack = MachineStack([1, 2])
        assert(mstack == [1, 2])

    @staticmethod
    def test_mstack_append_single_element():
        mstack = MachineStack()

        mstack.append(0)

        assert(mstack == [0])

    @staticmethod
    def test_mstack_append_multiple_elements():

        mstack = MachineStack()

        for i in range(mstack.STACK_LIMIT):
            mstack.append(1)

        with pytest.raises(StackOverflowException):
            mstack.append(1000)

    @staticmethod
    def test_mstack_pop():
        mstack = MachineStack([2])

        assert mstack.pop() == 2

        with pytest.raises(StackUnderflowException):
            mstack.pop()

    @staticmethod
    def test_mstack_no_support_add():
        mstack = MachineStack([0, 1])

        with pytest.raises(NotImplementedError):
            mstack = mstack + [2]

    @staticmethod
    def test_mstack_no_support_iadd():
        mstack = MachineStack()

        with pytest.raises(NotImplementedError):
            mstack += mstack

