from typing import List, Dict

from mythril.laser.ethereum.state import GlobalState


class Graph:
    def __init__(self):
        self.adjacency_list = dict()
        self.work_list = []

    def add_vertex(self, global_state: GlobalState):
        self.work_list.append(global_state)
        self.adjacency_list[global_state] = []

    def add_edges(self, from_vertex: GlobalState, to_vertices: List):

        self.adjacency_list[from_vertex] = []
        for to_vertex in to_vertices:
            self.work_list.append(to_vertex)
            self.adjacency_list[from_vertex].append(to_vertex)


class SimpleGraph:
    def __init__(self):
        self.work_list = []

    def add_vertex(self, global_state: GlobalState):
        self.work_list.append(global_state)

    def add_edges(self, global_state_in: GlobalState, global_states_out: GlobalState):
        self.work_list += global_states_out
