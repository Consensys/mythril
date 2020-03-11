from mythril.support.support_utils import Singleton


class Args(object, metaclass=Singleton):
    """
    This module helps in preventing args being sent through multiple of classes to reach any analysis/z
    """

    def __init__(self):
        self.solver_timeout = 10000


args = Args()
