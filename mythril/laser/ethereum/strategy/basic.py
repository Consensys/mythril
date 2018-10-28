"""
This module implements basic symbolic execution search strategies
"""
from ..state import GlobalState
from typing import List


class DepthFirstSearchStrategy:
    """
    Implements a depth first search strategy
    I.E. Follow one path to a leaf, and then continue to the next one
    """

    def __init__(self, work_list: List[GlobalState], max_depth: float):
        self.work_list = work_list
        self.max_depth = max_depth

    def __iter__(self):
        return self

    def __next__(self) -> GlobalState:
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


class BreadthFirstSearchStrategy:
    """
    Implements a breadth first search strategy
    I.E. Execute all states of a "level" before continuing
    """

    def __init__(self, work_list: List[GlobalState], max_depth: float):
        self.work_list = work_list
        self.max_depth = max_depth

    def __iter__(self) -> "BreadthFirstSearchStrategy":
        return self

    def __next__(self) -> GlobalState:
        """ Picks the next state to execute """
        try:
            # This strategies assumes that new states are appended at the end of the work_list
            # By taking the first element we effectively pick the "oldest" states, which amounts to bfs
            global_state = self.work_list.pop(0)
            if global_state.mstate.depth >= self.max_depth:
                return self.__next__()
            return global_state
        except IndexError:
            raise StopIteration()
