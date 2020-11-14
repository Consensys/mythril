"""This module implements basic symbolic execution search strategies."""
from random import randrange
from typing import List

from mythril.laser.ethereum.state.global_state import GlobalState
from mythril.laser.ethereum.strategy import BasicSearchStrategy


class ConcolicStrategy(BasicSearchStrategy):
    """Implements a depth first search strategy I.E.

    Follow one path to a leaf, and then continue to the next one
    """

    def __init__(self, work_list, max_depth, trace):
        super().__init__(work_list, max_depth)
        self.trace = trace
        self.trace_index = 0

    def get_strategic_global_state(self) -> GlobalState:
        """

        :return:
        """
        state = self.work_list.pop()
        if state.mstate.pc in self.trace:
            return state
