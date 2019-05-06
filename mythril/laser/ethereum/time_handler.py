import time
from mythril.support.support_utils import Singleton


class TimeHandler(object, metaclass=Singleton):
    def __init__(self):
        self._start_time = None
        self._transaction_start_time = None
        self._transaction_amount = None
        self._total_duration = None

    def reset_transaction_time(self):
        self._transaction_start_time = int(time.time() * 1000)

    def start_execution(self, execution_time: int, transaction_count: int):
        self._total_duration = execution_time
        self._transaction_amount = transaction_count

        self._start_time = int(time.time() * 1000)
        self._transaction_start_time = self._start_time

    def transaction_time_remaining(self):
        return min(
            self._transaction_start_time
            + (self._total_duration / self._transaction_amount)
            - time.time() * 1000,
            self._start_time + self._total_duration - time.time() * 1000,
        )


time_handler = TimeHandler()
