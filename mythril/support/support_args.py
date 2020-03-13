class Args:
    """
    This module helps in preventing args being sent through multiple of classes to reach
    any analysis/laser module
    """

    def __init__(self):
        self.solver_timeout = 10000
        self.sparse_pruning = True


args = Args()
