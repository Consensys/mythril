from mythril.analysis.modules.delegatecall import execute, _concrete_call, _symbolic_call
from mythril.analysis.ops import Call, Variable, VarType
from mythril.analysis.symbolic import SymExecWrapper
from laser.ethereum.svm import GlobalState, Node, Environment, Account
import pytest
from unittest.mock import MagicMock, patch
import pytest_mock


def test_concrete_call():
    # arrange
    address = "0x10"

    state = GlobalState(None, None)
    state.mstate.memory = ["placeholder", "calldata_bling_0"]

    node = Node("example")
    node.contract_name = "the contract name"
    node.function_name = "the function name"

    to = Variable(1, VarType.CONCRETE)
    meminstart = Variable(1, VarType.CONCRETE)
    call = Call(node, state, None, None, to, None)

    # act
    issues = _concrete_call(call, state, address, meminstart)

    # assert
    issue = issues[0]
    assert issue.address == address
    assert issue.contract == node.contract_name
    assert issue.function == node.function_name
    assert issue.title == "Call data forwarded with delegatecall()"
    assert issue.type == 'Informational'
    assert issue.description == "This contract forwards its call data via DELEGATECALL in its fallback function." \
                                " This means that any function in the called contract can be executed." \
                                " Note that the callee contract will have access to the storage of the " \
                                "calling contract.\n DELEGATECALL target: 0x1"


def test_concrete_call_symbolic_to():
    # arrange
    address = "0x10"

    state = GlobalState(None, None)
    state.mstate.memory = ["placeholder", "calldata_bling_0"]

    node = Node("example")
    node.contract_name = "the contract name"
    node.function_name = "the function name"

    to = Variable("calldata_3", VarType.SYMBOLIC)
    meminstart = Variable(1, VarType.CONCRETE)
    call = Call(node, state, None, None, to, None)

    # act
    issues = _concrete_call(call, state, address, meminstart)

    # assert
    issue = issues[0]
    assert issue.address == address
    assert issue.contract == node.contract_name
    assert issue.function == node.function_name
    assert issue.title == "Call data forwarded with delegatecall()"
    assert issue.type == 'Informational'
    assert issue.description == "This contract forwards its call data via DELEGATECALL in its fallback function." \
                                " This means that any function in the called contract can be executed." \
                                " Note that the callee contract will have access to the storage of the " \
                                "calling contract.\n DELEGATECALL target: calldata_3"


def test_concrete_call_not_calldata():
    # arrange
    state = GlobalState(None, None)
    state.mstate.memory = ["placeholder", "not_calldata"]
    meminstart = Variable(1, VarType.CONCRETE)

    # act
    issues = _concrete_call(None, state, None, meminstart)

    # assert
    assert issues == []


def test_symbolic_call_storage_to(mocker):
    # arrange
    address = "0x10"

    active_account = Account(address)
    environment = Environment(active_account, None, None, None, None, None)
    state = GlobalState(None, environment)
    state.mstate.memory = ["placeholder", "calldata_bling_0"]


    node = Node("example")
    node.contract_name = "the contract name"
    node.function_name = "the function name"

    to = Variable("storage_1", VarType.SYMBOLIC)
    call = Call(node, state, None, "Type: ", to, None)


    mocker.patch.object(SymExecWrapper, "__init__", lambda x, y: None)
    statespace = SymExecWrapper(1)

    mocker.patch.object(statespace, 'find_storage_write')
    statespace.find_storage_write.return_value = "Function name"


    # act
    issues = _symbolic_call(call, state, address, statespace)

    # assert
    issue = issues[0]
    assert issue.address == address
    assert issue.contract == node.contract_name
    assert issue.function == node.function_name
    assert issue.title == 'Type:  to a user-supplied address'
    assert issue.type == 'Informational'
    assert issue.description == 'This contract delegates execution to a contract address in storage slot 1.' \
                                ' This storage slot can be written to by calling the function `Function name`. ' \
                                'Be aware that the called contract gets unrestricted access to this contract\'s state.'


def test_symbolic_call_calldata_to(mocker):
    # arrange
    address = "0x10"

    state = GlobalState(None, None)
    state.mstate.memory = ["placeholder", "calldata_bling_0"]


    node = Node("example")
    node.contract_name = "the contract name"
    node.function_name = "the function name"

    to = Variable("calldata", VarType.SYMBOLIC)
    call = Call(node, state, None, "Type: ", to, None)


    mocker.patch.object(SymExecWrapper, "__init__", lambda x, y: None)
    statespace = SymExecWrapper(1)

    mocker.patch.object(statespace, 'find_storage_write')
    statespace.find_storage_write.return_value = "Function name"


    # act
    issues = _symbolic_call(call, state, address, statespace)

    # assert
    issue = issues[0]
    assert issue.address == address
    assert issue.contract == node.contract_name
    assert issue.function == node.function_name
    assert issue.title == 'Type:  to a user-supplied address'
    assert issue.type == 'Informational'
    assert issue.description == 'This contract delegates execution to a contract address obtained from calldata. ' \
                                'Be aware that the called contract gets unrestricted access to this contract\'s state.'


@patch('laser.ethereum.svm.GlobalState.get_current_instruction')
@patch('mythril.analysis.modules.delegatecall._concrete_call')
@patch('mythril.analysis.modules.delegatecall._symbolic_call')
def test_delegate_call(sym_mock, concrete_mock, curr_instruction):
    # arrange
    # sym_mock = mocker.patch.object(delegatecall, "_symbolic_call")
    # concrete_mock = mocker.patch.object(delegatecall, "_concrete_call")
    sym_mock.return_value = []
    concrete_mock.return_value = []
    curr_instruction.return_value = {'address': '0x10'}

    active_account = Account('0x10')
    environment = Environment(active_account, None, None, None, None, None)
    state = GlobalState(None, environment)
    state.mstate.memory = ["placeholder", "calldata_bling_0"]
    state.mstate.stack = [1, 2, 3]
    assert state.get_current_instruction() == {'address': '0x10'}

    node = Node("example")
    node.contract_name = "the contract name"
    node.function_name = "fallback"

    to = Variable("storage_1", VarType.SYMBOLIC)
    call = Call(node, state, None, "DELEGATECALL", to, None)

    statespace = MagicMock()
    statespace.calls = [call]

    # act
    issues = execute(statespace)

    # assert
    assert concrete_mock.call_count == 1
    assert sym_mock.call_count == 1


@patch('mythril.analysis.modules.delegatecall._concrete_call')
@patch('mythril.analysis.modules.delegatecall._symbolic_call')
def test_delegate_call_not_delegate(sym_mock, concrete_mock):
    # arrange
    # sym_mock = mocker.patch.object(delegatecall, "_symbolic_call")
    # concrete_mock = mocker.patch.object(delegatecall, "_concrete_call")
    sym_mock.return_value = []
    concrete_mock.return_value = []

    node = Node("example")
    node.function_name = "fallback"

    to = Variable("storage_1", VarType.SYMBOLIC)
    call = Call(node, None, None, "NOT_DELEGATECALL", to, None)

    statespace = MagicMock()
    statespace.calls = [call]

    # act
    issues = execute(statespace)

    # assert
    assert issues == []
    assert concrete_mock.call_count == 0
    assert sym_mock.call_count == 0


@patch('mythril.analysis.modules.delegatecall._concrete_call')
@patch('mythril.analysis.modules.delegatecall._symbolic_call')
def test_delegate_call_not_fallback(sym_mock, concrete_mock):
    # arrange
    # sym_mock = mocker.patch.object(delegatecall, "_symbolic_call")
    # concrete_mock = mocker.patch.object(delegatecall, "_concrete_call")
    sym_mock.return_value = []
    concrete_mock.return_value = []

    node = Node("example")
    node.function_name = "not_fallback"

    to = Variable("storage_1", VarType.SYMBOLIC)
    call = Call(node, None, None, "DELEGATECALL", to, None)

    statespace = MagicMock()
    statespace.calls = [call]

    # act
    issues = execute(statespace)

    # assert
    assert issues == []
    assert concrete_mock.call_count == 0
    assert sym_mock.call_count == 0
