from mythril.laser.ethereum.taint_analysis import *


def test_mutate_not_tainted():
    # Arrange
    record = TaintRecord()

    record.stack = [True, False, False]
    # Act
    TaintRunner.mutate_stack(record, (2, 1))

    # Assert
    assert record.stack_tainted(0)
    assert record.stack_tainted(1) is False
    assert record.stack == [True, False]


def test_mutate_tainted():
    # Arrange
    record = TaintRecord()

    record.stack = [True, False, True]

    # Act
    TaintRunner.mutate_stack(record, (2, 1))

    # Assert
    assert record.stack_tainted(0)
    assert record.stack_tainted(1)
    assert record.stack == [True, True]
