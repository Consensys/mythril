"""This module contains general exceptions used by Mythril."""


class MythrilBaseException(Exception):
    """The Mythril exception base type."""

    pass


class CompilerError(MythrilBaseException):
    """A Mythril exception denoting an error during code compilation."""

    pass


class UnsatError(MythrilBaseException):
    """A Mythril exception denoting the unsatisfiability of a series of constraints."""

    pass


class NoContractFoundError(MythrilBaseException):
    """A Mythril exception denoting that a given contract file was not found."""

    pass


class CriticalError(MythrilBaseException):
    """A Mythril exception denoting an unknown critical error has been encountered."""

    pass


class AddressNotFoundError(MythrilBaseException):
    """A Mythril exception denoting the given smart contract address was not found."""

    pass
