"""
This module implements basic symbolic execution search strategies
"""


class DepthFirstSearchStrategy:
    """
    Implements a depth first search strategy
    I.E. Follow one path to a leaf, and then continue to the next one
    """
    def __init__(self, work_list, max_depth):
        self.work_list = work_list
        self.max_depth = max_depth

    def __iter__(self):
        return self

    def __next__(self):
        """ Picks the next state to execute """
        try:
            # This strategies assumes that new states are appended at the end of the work_list
            # By taking the last element we effectively pick the "newest" states, which amounts to dfs
            global_state = self.work_list.pop()
            if global_state.mstate.depth >= self.max_depth:
                return self.__next__()
            return global_state
        except IndexError:
            raise StopIteration()

