class Args:
    """
    This module helps in preventing args being sent through multiple of classes to reach
    any analysis/laser module
    """

    def __init__(self):
        self.solver_timeout = 10000
        self.sparse_pruning = True
        self.unconstrained_storage = False
        self.parallel_solving = False
        self.call_depth_limit = 3
        self.iprof = True
        self.solver_log = None


args = Args()
