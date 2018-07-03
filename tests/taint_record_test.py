from mythril.laser.ethereum.taint_analysis import *


def test_record_tainted_check():
    # arrange
    record = TaintRecord()
    record.stack = [True, False, True]

    # act
    tainted = record.stack_tainted(2)

    # assert
    assert tainted is True


def test_record_untainted_check():
    # arrange
    record = TaintRecord()
    record.stack = [True, False, False]

    # act
    tainted = record.stack_tainted(2)

    # assert
    assert tainted is False


def test_record_untouched_check():
    # arrange
    record = TaintRecord()

    # act
    tainted = record.stack_tainted(3)

    # assert
    assert tainted is None
