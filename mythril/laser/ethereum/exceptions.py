class VmException(Exception):
    pass


class StackUnderflowException(VmException):
    pass


class StopSignal(Exception):
    pass
