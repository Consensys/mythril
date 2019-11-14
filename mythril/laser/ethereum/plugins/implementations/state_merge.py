from copy import copy
from typing import List
from mythril.laser.ethereum.svm import LaserEVM
from mythril.laser.ethereum.plugins.plugin import LaserPlugin
from mythril.laser.smt import symbol_factory, simplify, Or
from mythril.laser.ethereum.state.world_state import WorldState
import logging
import z3

log = logging.getLogger(__name__)


class StateMerge(LaserPlugin):
    def initialize(self, symbolic_vm: LaserEVM):
        """Initializes the mutation pruner

        Introduces hooks for SSTORE operations
        :param symbolic_vm:
        :return:
        """

        @symbolic_vm.laser_hook("stop_sym_trans")
        def execute_stop_sym_trans_hook(svm: LaserEVM):
            log.info(svm.open_states)

            open_states = svm.open_states

            if len(open_states) <= 1:
                return
            num_old_states = len(open_states)
            new_states = []  # type: List[WorldState]
            old_size = len(open_states)
            old_states = copy(open_states)
            while old_size != len(new_states):
                old_size = len(new_states)
                i = 0
                new_states = []
                while i < len(old_states) - 1:
                    if self.check_merge_condition(old_states[i], old_states[i + 1]):
                        new_states.append(
                            self.merge_states(old_states[i], old_states[i + 1])
                        )
                        i += 2
                        continue
                    else:
                        new_states.append(old_states[i])
                    i += 1
                if i == len(old_states) - 1:
                    new_states.append(old_states[i])
                old_states = copy(new_states)

            logging.info(
                "States reduced from {} to {}".format(num_old_states, len(new_states))
            )
            svm.open_states = new_states

    @staticmethod
    def check_merge_condition(state1: WorldState, state2: WorldState):
        basic_condition = state1.check_merge_condition(state2)
        return basic_condition

    @staticmethod
    def merge_states(state1: WorldState, state2: WorldState) -> WorldState:
        state1.merge_states(state2)
        return state1
