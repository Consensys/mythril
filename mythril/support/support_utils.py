"""This module contains utility functions for the Mythril support package."""
from typing import Dict

class Singleton(type):
    """A metaclass type implementing the singleton pattern."""

    _instances = {}  # type: Dict

    def __call__(cls, *args, **kwargs):
        """Delegate the call to an existing resource or a a new one.

        This is not thread- or process-safe by default. It must be protected with
        a lock.

        :param args:
        :param kwargs:
        :return:
        """
        if cls not in cls._instances:
            cls._instances[cls] = super(Singleton, cls).__call__(*args, **kwargs)
        return cls._instances[cls]
