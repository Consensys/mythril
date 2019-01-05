"""This module contains EVM exception types used by LASER."""


class VmException(Exception):
    """The base VM exception type."""

    pass


class StackUnderflowException(IndexError, VmException):
    """A VM exception regarding stack underflows."""

    pass


class StackOverflowException(VmException):
    """A VM exception regarding stack overflows."""

    pass


class InvalidJumpDestination(VmException):
    """A VM exception regarding JUMPs to invalid destinations."""

    pass


class InvalidInstruction(VmException):
    """A VM exception denoting an invalid op code has been encountered."""

    pass


class OutOfGasException(VmException):
    """A VM exception denoting the current execution has run out of gas."""

    pass
