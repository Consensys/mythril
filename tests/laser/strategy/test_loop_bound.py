import pytest
from mythril.laser.ethereum.strategy.extensions.bounded_loops import (
    BoundedLoopsStrategy,
)


@pytest.mark.parametrize(
    "trace, count",
    [
        ([6, 7, 7, 7], 3),
        ([6, 8, 6, 7, 6, 7, 6, 7, 6, 7], 4),
        ([6, 6, 6, 6], 4),
        ([6, 7, 8] * 10, 10),
        ([7, 9, 10] + list(range(1, 100)) * 100, 100),
        ([7, 10, 15], 0),
        ([7] * 100, 100),
    ],
)
def test_loop_count(trace, count):
    assert count == BoundedLoopsStrategy.get_loop_count(trace)
