from abc import ABC, abstractmethod


class ExecutionInfo(ABC):
    @abstractmethod
    def as_dict(self):
        """Returns a dictionary with the execution info contained in this object

        The returned dictionary only uses primitive types.
        """
        pass
