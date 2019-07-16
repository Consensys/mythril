from mythril.support.support_utils import Singleton


class AnalysisArgs(object, metaclass=Singleton):
    """
    This module helps in preventing args being sent through multiple of classes to reach analysis modules
    """

    def __init__(self):
        self._loop_bound = 4
        self._solver_timeout = 100000

    def set_loop_bound(self, loop_bound: int):
        self._loop_bound = loop_bound

    def set_solver_timeout(self, solver_timeout: int):
        self._solver_timeout = solver_timeout

    @property
    def loop_bound(self):
        return self._loop_bound

    @property
    def solver_timeout(self):
        return self._solver_timeout


analysis_args = AnalysisArgs()
