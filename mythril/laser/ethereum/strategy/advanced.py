from random import shuffle
from copy import copy
from typing import List

from . import AdvancedSearchStrategy
from mythril.laser.ethereum.graph import Graph
from mythril.laser.ethereum.state import GlobalState


class RandomBranchDepthFirstSearch(AdvancedSearchStrategy):
    """
    Implements a depth first search strategy with choice of branch randomly chosen
    I.E. Follow one path to a leaf, and then continue to the next one
    """
    __slots__ = 'stack'

    def __init__(self, graph: Graph, max_depth: int):
        super(RandomBranchDepthFirstSearch, self).__init__(graph, max_depth)

    def get_strategic_global_state(self) -> GlobalState:

        if not self.graph.work_list:
            raise IndexError

        try:
            edge_list: List = copy(self.graph.adjacency_list[self.graph.work_list[-1]])
        except KeyError:
            edge_list = []
        shuffle(edge_list)
        self.graph.work_list += edge_list

        self.current_vertex = self.graph.work_list.pop()
        return self.current_vertex
