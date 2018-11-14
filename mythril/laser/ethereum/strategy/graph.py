from typing import List
from copy import copy
from abc import ABC, abstractmethod

from mythril.laser.ethereum.state import GlobalState


class BaseGraph(ABC):
    @abstractmethod
    def add_vertex(self, global_state: GlobalState):
        raise NotImplementedError("Must be implemented by a subclass")

    @abstractmethod
    def add_edges(self, global_state_in: GlobalState, global_state_out: GlobalState):
        raise NotImplementedError("Must be implemented by a subclass")


class Graph(BaseGraph):
    def __init__(self):
        self.adjacency_list = dict()
        self.work_list = []

    def add_vertex(self, global_state: GlobalState):
        self.work_list.append(global_state)
        self.adjacency_list[global_state] = []

    def add_edges(self, from_vertex: GlobalState, to_vertices: List):
        if from_vertex not in self.adjacency_list.keys():
            self.adjacency_list[from_vertex] = []
            self.work_list.append(from_vertex)

        for to_vertex in to_vertices:
            self.work_list.append(to_vertex)
            self.adjacency_list[from_vertex].append(to_vertex)

    def get_current_edge_list(self):
        try:
            return copy(self.graph.adjacency_list[self.graph.work_list[-1]])
        except KeyError:
            return []


class SimpleGraph(BaseGraph):
    def __init__(self):
        self.work_list = []

    def add_vertex(self, global_state: GlobalState):
        self.work_list.append(global_state)

    def add_edges(self, global_state_in: GlobalState, global_states_out: GlobalState):
        self.work_list += global_states_out
