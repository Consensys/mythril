import time


class TimeHandler:
    def __init__(self):
        self._start_time = None
        self._execution_time = None

    def start_execution(self, execution_time):
        self._start_time = int(time.time() * 1000)
        self._execution_time = execution_time * 1000

    def time_remaining(self):
        return self._execution_time - (int(time.time() * 1000) - self._start_time)


time_handler = TimeHandler()
