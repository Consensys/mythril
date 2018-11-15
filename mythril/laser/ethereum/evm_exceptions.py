class VmException(Exception):
    pass


class StackUnderflowException(IndexError, VmException):
    pass


class StackOverflowException(VmException):
    pass


class InvalidJumpDestination(VmException):
    pass


class InvalidInstruction(VmException):
    pass


class OutOfGasException(VmException):
    pass
