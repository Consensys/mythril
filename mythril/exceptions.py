class MythrilBaseException(Exception):
    pass


class CompilerError(MythrilBaseException):
    pass


class UnsatError(MythrilBaseException):
    pass


class NoContractFoundError(MythrilBaseException):
    pass


class CriticalError(MythrilBaseException):
    pass


class AddressNotFoundError(MythrilBaseException):
    pass
