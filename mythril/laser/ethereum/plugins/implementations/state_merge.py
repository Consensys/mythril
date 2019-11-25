from copy import copy
from typing import Dict, List
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
                new_states = []
                merged_dict = {}  # type: Dict[int, bool]
                for i in range(len(old_states)):
                    if merged_dict.get(i, False):
                        continue
                    i_is_merged = False
                    for j in range(i + 1, len(old_states)):
                        if merged_dict.get(j, False) or not self.check_merge_condition(
                            old_states[i], old_states[j]
                        ):
                            j += 1
                            continue
                        state = old_states[i]
                        self.merge_states(state, old_states[j])
                        merged_dict[j] = True
                        new_states.append(state)
                        i_is_merged = True
                        break

                    if i_is_merged is False:
                        new_states.append(old_states[i])

                old_states = copy(new_states)
            logging.info(
                "States reduced from {} to {}".format(num_old_states, len(new_states))
            )
            svm.open_states = new_states

    @staticmethod
    def check_merge_condition(state1: WorldState, state2: WorldState):
        """
        Check whether two world states can be merged
        :param state1:
        :param state2:
        :return: whether the states can be merged or not
        """
        basic_condition = state1.check_merge_condition(state2)
        return basic_condition

    @staticmethod
    def merge_states(state1: WorldState, state2: WorldState) -> WorldState:
        """
        Merge state2 into state1
        :param state1: The state to be merged into
        :param state2: The state which is merged into state1
        :return:
        """
        state1.merge_states(state2)
        return state1
