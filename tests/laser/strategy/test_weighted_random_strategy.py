import pytest
import random
from mythril.laser.ethereum.state import GlobalState, MachineState
from mythril.laser.ethereum.strategy.basic import ReturnWeightedRandomStrategy
from mythril.laser.ethereum.strategy.graph import SimpleGraph


test_worklist_input = [
    (
        [
            GlobalState(None, None, None, machine_state=MachineState(gas=100, depth=2)),
            GlobalState(None, None, None, machine_state=MachineState(gas=100, depth=10)),
            GlobalState(None, None, None, machine_state=MachineState(gas=100, depth=20)),
        ]
    )
]


@pytest.mark.parametrize("work_list", test_worklist_input)
def test_random_weighted_strategy(work_list):
    strategy = ReturnWeightedRandomStrategy(SimpleGraph(), max_depth=30)
    strategy.graph.work_list = work_list
    counter = {}
    iterations = 10000
    eps = 1e-2
    random.seed(1)
    total_sum = sum([1/(1+global_state.mstate.depth) for global_state in work_list])
    for i in range(iterations):
        global_state = strategy.get_strategic_global_state()
        counter[global_state.mstate.depth] = counter.get(global_state.mstate.depth, 0) + 1
        strategy.graph.work_list.append(global_state)
    for key in counter.keys():
        assert abs(counter[key]/iterations - 1/((key+1)*total_sum)) < eps

