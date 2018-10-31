from abc import ABC, abstractmethod

from mythril.laser.ethereum.graph import SimpleGraph, Graph


class BasicSearchStrategy(ABC):
    __slots__ = 'graph', 'max_depth'

    def __init__(self, graph: SimpleGraph, max_depth: int):
        self.graph = graph
        self.max_depth = max_depth

    def __iter__(self):
        return self

    @abstractmethod
    def get_strategic_global_state(self):
        raise NotImplementedError("Must be implemented by a subclass")

    def __next__(self):
        try:
            global_state = self.get_strategic_global_state()
            if global_state.mstate.depth >= self.max_depth:
                return self.__next__()
            return global_state
        except IndexError:
            raise StopIteration


class AdvancedSearchStrategy(ABC):
    __slots__ = 'graph', 'max_depth', 'current_vertex'

    def __init__(self, graph: Graph, max_depth: int):
        self.graph = graph
        self.max_depth = max_depth
        self.current_vertex = 0

    def __iter__(self):
        return self

    @abstractmethod
    def get_strategic_global_state(self):
        raise NotImplementedError("Must be implemented by a subclass")

    def __next__(self):
        try:
            global_state = self.get_strategic_global_state()
            if global_state.mstate.depth >= self.max_depth:
                return self.__next__()
            return global_state
        except IndexError:
            raise StopIteration
