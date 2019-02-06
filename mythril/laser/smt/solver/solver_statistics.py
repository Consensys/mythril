from time import time

from mythril.support.support_utils import Singleton

from typing import Callable


def stat_smt_query(func: Callable):
    stat_store = SolverStatistics()

    def function_wrapper(*args, **kwargs):
        if not stat_store.enabled:
            return func(*args, **kwargs)

        stat_store.query_count += 1
        begin = time()

        result = func(*args, **kwargs)

        end = time()
        stat_store.solver_time += end - begin

        return result

    return function_wrapper


class SolverStatistics(object, metaclass=Singleton):
    def __init__(self):
        self.enabled = False
        self.query_count = 0
        self.solver_time = 0

    def __repr__(self):
        return "Query count: {} \nSolver time: {}".format(
            self.query_count, self.solver_time
        )
