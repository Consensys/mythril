import pytest
from mythril.laser.ethereum.strategy.graph import SimpleGraph
from mythril.laser.ethereum.state import GlobalState

add_vertex_test_data = [GlobalState(None, None, None)]


@pytest.mark.parametrize("vertex", add_vertex_test_data)
def test_add_vertex(vertex):
    graph = SimpleGraph()
    graph.add_vertex(vertex)
    assert graph.work_list[-1] == vertex


add_edge_test_data = [(GlobalState(None, None, None), [GlobalState(None, None, None), GlobalState(None, None, None)])]


@pytest.mark.parametrize("vertex_from, vertices_to", add_edge_test_data)
def test_add_edges(vertex_from, vertices_to):
    graph = SimpleGraph()
    graph.add_edges(vertex_from, vertices_to)

    assert graph.work_list == vertices_to
