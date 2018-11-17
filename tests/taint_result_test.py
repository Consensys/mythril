from mythril.laser.ethereum.taint_analysis import *
from mythril.laser.ethereum.state.global_state import GlobalState


def test_result_state():
    # arrange
    taint_result = TaintResult()
    record = TaintRecord()
    state = GlobalState(2, None, None)
    state.mstate.stack = [1, 2, 3]
    record.add_state(state)
    record.stack = [False, False, False]
    # act
    taint_result.add_records([record])
    tainted = taint_result.check(state, 2)

    # assert
    assert tainted is False
    assert record in taint_result.records


def test_result_no_state():
    # arrange
    taint_result = TaintResult()
    record = TaintRecord()
    state = GlobalState(2, None, None)
    state.mstate.stack = [1, 2, 3]

    # act
    taint_result.add_records([record])
    tainted = taint_result.check(state, 2)

    # assert
    assert tainted is None
    assert record in taint_result.records
