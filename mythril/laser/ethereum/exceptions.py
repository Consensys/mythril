class VmException(Exception):
    pass


class StackUnderflowException(VmException):
    pass


class StackOverflowException(VmException):
    pass


class StopSignal(Exception):
    pass
