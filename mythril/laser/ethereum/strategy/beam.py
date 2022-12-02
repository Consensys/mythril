from typing import List

from mythril.laser.ethereum.state.global_state import GlobalState
from . import BasicSearchStrategy


class BeamSearch(BasicSearchStrategy):
    """chooses a random state from the worklist with equal likelihood."""

    def __init__(self, work_list, max_depth, beam_width, **kwargs):
        super().__init__(work_list, max_depth)
        self.beam_width = beam_width

    @staticmethod
    def beam_priority(state):
        return sum([annotation.search_importance for annotation in state._annotations])

    def sort_and_eliminate_states(self):
        self.work_list.sort(key=lambda state: self.beam_priority(state), reverse=True)
        del self.work_list[self.beam_width :]

    def view_strategic_global_state(self) -> GlobalState:
        """

        :return:
        """
        self.sort_and_eliminate_states()
        if len(self.work_list) > 0:
            return self.work_list[0]
        else:
            raise IndexError

    def get_strategic_global_state(self) -> GlobalState:
        """

        :return:
        """
        self.sort_and_eliminate_states()
        if len(self.work_list) > 0:
            return self.work_list.pop(0)
        else:
            raise IndexError
