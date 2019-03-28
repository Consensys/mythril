import time
from mythril.support.support_utils import Singleton


class TimeHandler(object, metaclass=Singleton):
    def __init__(self):
        self._start_time = None
        self._transaction_execution_timeout = None

    def reset_start_time(self):
        self._start_time = int(time.time() * 1000)

    def start_execution(self, execution_time: int, transaction_count: int):
        self._start_time = int(time.time() * 1000)
        self._transaction_execution_timeout = (
            execution_time * 1000 // (1 + transaction_count)
        )

    def transaction_time_remaining(self):
        return self._transaction_execution_timeout - (
            int(time.time() * 1000) - self._start_time
        )


time_handler = TimeHandler()
