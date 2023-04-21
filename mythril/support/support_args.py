from typing import List
from mythril.support.support_utils import Singleton


class Args(object, metaclass=Singleton):
    """
    This module helps in preventing args being sent through multiple of classes to reach
    any analysis/laser module
    """

    def __init__(self):
        self.solver_timeout = 10000
        self.pruning_factor = None
        self.unconstrained_storage = False
        self.parallel_solving = False
        self.call_depth_limit = 3
        self.iprof = True
        self.solver_log = None
        self.transaction_sequences: List[List[str]] = None
        self.use_integer_module = True
        self.use_issue_annotations = False
        self.solc_args = None


args = Args()
