from abc import ABC, abstractmethod


class BasicSearchStrategy(ABC):
    """"""

    __slots__ = "work_list", "max_depth"

    def __init__(self, work_list, max_depth):
        self.work_list = work_list
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
        except IndexError:
            raise StopIteration
