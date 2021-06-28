from abc import ABC, abstractmethod
from typing import List
from mythril.laser.ethereum.state.global_state import GlobalState


class BasicSearchStrategy(ABC):
    """
    A basic search strategy which halts based on depth
    """

    def __init__(self, work_list, max_depth):
        self.work_list = work_list  # type: List[GlobalState]
        self.max_depth = max_depth

    def __iter__(self):
        return self

    @abstractmethod
    def get_strategic_global_state(self):
        """"""
        raise NotImplementedError("Must be implemented by a subclass")

    def __next__(self):
        try:
            global_state = self.get_strategic_global_state()
            if global_state.mstate.depth >= self.max_depth:
                return self.__next__()
            return global_state
        except (IndexError, StopIteration):
            raise StopIteration


class CriterionSearchStrategy(BasicSearchStrategy):
    """
    If a criterion is satisfied, the search halts
    """

    def __init__(self, work_list, max_depth):
        super().__init__(work_list, max_depth)
        self.satisfied_criterion = False

    def __next__(self):
        if self.satisfied_criterion:
            raise StopIteration
        return super().__next__()
