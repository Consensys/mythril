import mock
import pytest
from pytest_mock import mocker
from mythril.laser.ethereum.taint_analysis import *
from mythril.laser.ethereum.svm import GlobalState, Node, Edge, LaserEVM
from mythril.laser.ethereum.state import MachineState


def test_execute_state(mocker):
    record = TaintRecord()
    record.stack = [True, False, True]

    state = GlobalState(None, None)
    state.mstate.stack = [1, 2, 3]
    mocker.patch.object(state, 'get_current_instruction')
    state.get_current_instruction.return_value = {"opcode": "ADD"}

    # Act
    new_record = TaintRunner.execute_state(record, state)

    # Assert
    assert new_record.stack == [True, True]
    assert record.stack == [True, False, True]


def test_execute_node(mocker):
    record = TaintRecord()
    record.stack = [True, True, False, False]

    state_1 = GlobalState(None, None)
    state_1.mstate.stack = [1, 2, 3]
    state_1.mstate.pc = 1
    mocker.patch.object(state_1, 'get_current_instruction')
    state_1.get_current_instruction.return_value = {"opcode": "SWAP1"}

    state_2 = GlobalState(None, 1)
    state_2.mstate.stack = [1, 2, 4, 1]
    mocker.patch.object(state_2, 'get_current_instruction')
    state_2.get_current_instruction.return_value = {"opcode": "ADD"}

    node = Node("Test contract")
    node.states = [state_1, state_2]

    # Act
    records = TaintRunner.execute_node(node, record)

    # Assert
    assert len(records) == 2

    assert records[0].stack == [True, True, False, False]
    assert records[1].stack == [True, True, False]

    assert state_2 in records[0].states
    assert state_1 in record.states




def test_execute(mocker):
    state_1 = GlobalState(None, None, MachineState(gas=10000000))
    state_1.mstate.stack = [1, 2]
    mocker.patch.object(state_1, 'get_current_instruction')
    state_1.get_current_instruction.return_value = {"opcode": "PUSH"}

    state_2 = GlobalState(None, None, MachineState(gas=10000000))
    state_2.mstate.stack = [1, 2, 3]
    mocker.patch.object(state_2, 'get_current_instruction')
    state_2.get_current_instruction.return_value = {"opcode": "ADD"}

    node_1 = Node("Test contract")
    node_1.states = [state_1, state_2]

    state_3 = GlobalState(None, None, MachineState(gas=10000000))
    state_3.mstate.stack = [1, 2]
    mocker.patch.object(state_3, 'get_current_instruction')
    state_3.get_current_instruction.return_value = {"opcode": "ADD"}

    node_2 = Node("Test contract")
    node_2.states = [state_3]

    edge = Edge(node_1.uid, node_2.uid)

    statespace = LaserEVM(None)
    statespace.edges = [edge]
    statespace.nodes[node_1.uid] = node_1
    statespace.nodes[node_2.uid] = node_2

    # Act
    result = TaintRunner.execute(statespace, node_1, state_1, [True, True])

    # Assert
    print(result)
    assert len(result.records) == 3
    assert result.records[2].states == []
    assert state_3 in result.records[1].states
