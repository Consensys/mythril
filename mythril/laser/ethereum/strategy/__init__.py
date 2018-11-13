from abc import ABC, abstractmethod

from mythril.laser.ethereum.strategy.graph import SimpleGraph, Graph


class BasicSearchStrategy(ABC):
    """
    The strategies where we don't need to keep tract of the entire Graph and can just go with a simple worklist
    """
    __slots__ = "graph", "max_depth"

    def __init__(self, graph: SimpleGraph, max_depth: int):
        assert isinstance(graph, SimpleGraph)
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
    """
    The strategies which requires us to maintain an adjacency list based graph and the current vertex in the traversal
    """
    __slots__ = "graph", "max_depth", "current_vertex"

    def __init__(self, graph: Graph, max_depth: int):
        assert isinstance(graph, Graph)
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
