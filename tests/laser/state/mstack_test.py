from mythril.laser.ethereum.state import MachineStack
from mythril.laser.ethereum.evm_exceptions import *
from tests import BaseTestCase


class MachineStackTest(BaseTestCase):

    @staticmethod
    def test_mstack_constructor():
        mstack = MachineStack([1, 2])
        assert(mstack == [1, 2])

        mstack = MachineStack([])
        assert(mstack == [])

    @staticmethod
    def test_mstack_append():
        mstack = MachineStack([])
        mstack.append(0)
        assert(mstack == [0])

        for i in range(mstack.STACK_LIMIT-1):
            mstack.append(1)

        try:
            mstack.append(1000)
        except StackOverflowException:
            return

        assert False

    @staticmethod
    def test_mstack_pop():
        mstack = MachineStack([0])

        mstack.append(110)
        assert mstack.pop() == 110

        mstack.append(111)
        assert mstack.pop(0) == 0

        assert mstack.pop() == 111

        try:
            mstack.pop()
        except StackUnderflowException:
            return

        assert False

    @staticmethod
    def test_mstack_no_support():
        mstack = MachineStack([0, 1])
        success = False
        try:
            mstack += [0]
        except NotImplementedError:
            success = True

        assert success

        try:
            mstack = mstack + [0]
        except NotImplementedError:
            return

        assert False

