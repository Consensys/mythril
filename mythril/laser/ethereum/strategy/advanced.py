from random import shuffle

from . import AdvancedSearchStrategy
from mythril.laser.ethereum.strategy.graph import Graph
from mythril.laser.ethereum.state import GlobalState


class RandomBranchDepthFirstSearch(AdvancedSearchStrategy):
    """
    Implements a depth first search strategy with choice of branch randomly chosen
    I.E. Follow one path to a leaf, and then continue to the next one
    """

    __slots__ = "stack"

    def __init__(self, graph: Graph, max_depth: int):
        super(RandomBranchDepthFirstSearch, self).__init__(graph, max_depth)

    def get_strategic_global_state(self) -> GlobalState:

        edge_list = self.graph.get_current_edge_list()
        shuffle(edge_list)
        self.graph.work_list += edge_list

        self.current_vertex = self.graph.work_list.pop()
        return self.current_vertex
