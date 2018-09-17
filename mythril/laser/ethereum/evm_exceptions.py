class VmException(Exception):
    pass


class StackUnderflowException(IndexError, VmException):
    pass


class StackOverflowException(VmException):
    pass



