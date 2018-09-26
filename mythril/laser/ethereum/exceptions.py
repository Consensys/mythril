class VmException(Exception):
    pass


class StackUnderflowException(VmException):
    pass


class InvalidJumpDestination(VmException):
    pass


class StopSignal(Exception):
    pass

