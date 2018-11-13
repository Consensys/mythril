import pytest
from mythril.laser.ethereum.strategy.graph import Graph
from mythril.laser.ethereum.state import GlobalState

add_vertex_test_data = [GlobalState(None, None, None)]


@pytest.mark.parametrize("vertex", add_vertex_test_data)
def test_add_vertex(vertex):
    graph = Graph()
    graph.add_vertex(vertex)
    assert vertex in graph.adjacency_list


add_edge_test_data = [
    (
        GlobalState(None, None, None),
        [GlobalState(None, None, None), GlobalState(None, None, None)],
    )
]


@pytest.mark.parametrize("vertex_from, vertices_to", add_edge_test_data)
def test_add_edges(vertex_from, vertices_to):
    graph = Graph()
    graph.add_edges(vertex_from, vertices_to)

    assert graph.adjacency_list[vertex_from] == vertices_to


root_vertex = GlobalState(None, None, None)
add_multiple_edges_test_data = [
    (
        (root_vertex, [GlobalState(None, None, None)]),
        (root_vertex, [GlobalState(None, None, None), GlobalState(None, None, None)]),
    )
]


@pytest.mark.parametrize("edge_list1, edge_list2", add_multiple_edges_test_data)
def test_add_edges_multiple_times(edge_list1, edge_list2):
    graph = Graph()
    graph.add_edges(edge_list1[0], edge_list1[1])
    graph.add_edges(edge_list2[0], edge_list2[1])

    assert graph.adjacency_list[edge_list1[0]] == edge_list1[1] + edge_list2[1]
