import pytest
from mythril.laser.ethereum.strategy.beam import (
    BeamSearch,
)
from mythril.disassembler.disassembly import Disassembly
from mythril.laser.ethereum.state.environment import Environment
from mythril.laser.ethereum.state.machine_state import MachineState
from mythril.laser.ethereum.state.global_state import GlobalState
from mythril.laser.ethereum.state.world_state import WorldState
from mythril.analysis.potential_issues import PotentialIssuesAnnotation

world_state = WorldState()
account = world_state.create_account(balance=10, address=101)
account.code = Disassembly("60606040")
environment = Environment(account, None, None, None, None, None, None)
potential_issues = PotentialIssuesAnnotation()
# It is a hassle to construct multiple issues
potential_issues.potential_issues = [0, 0]


@pytest.mark.parametrize(
    "state, priority",
    [
        (
            GlobalState(
                world_state,
                environment,
                None,
                MachineState(gas_limit=8000000),
                annotations=[PotentialIssuesAnnotation()],
            ),
            0,
        ),
        (
            GlobalState(
                world_state,
                environment,
                None,
                MachineState(gas_limit=8000000),
                annotations=[potential_issues],
            ),
            20,
        ),
    ],
)
def test_priority_sum(state, priority):
    assert priority == BeamSearch.beam_priority(state)


@pytest.mark.parametrize(
    "states, width",
    [
        (
            [
                GlobalState(
                    world_state,
                    environment,
                    None,
                    MachineState(gas_limit=8000000),
                    annotations=[PotentialIssuesAnnotation()],
                ),
                GlobalState(
                    world_state,
                    environment,
                    None,
                    MachineState(gas_limit=8000000),
                    annotations=[potential_issues],
                ),
            ],
            1,
        ),
        (
            100
            * [
                GlobalState(
                    world_state,
                    environment,
                    None,
                    MachineState(gas_limit=8000000),
                    annotations=[PotentialIssuesAnnotation()],
                )
            ],
            1,
        ),
        (
            100
            * [
                GlobalState(
                    world_state,
                    environment,
                    None,
                    MachineState(gas_limit=8000000),
                    annotations=[PotentialIssuesAnnotation()],
                )
            ],
            0,
        ),
    ],
)
def test_elimination(states, width):
    strategy = BeamSearch(states, max_depth=100, beam_width=width)
    strategy.sort_and_eliminate_states()

    assert len(strategy.work_list) <= width
    for i in range(len(strategy.work_list) - 1):
        assert strategy.beam_priority(strategy.work_list[i]) >= strategy.beam_priority(
            strategy.work_list[i + 1]
        )
