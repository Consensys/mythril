from copy import copy
from typing import Set, List
from mythril.laser.ethereum.svm import LaserEVM
from mythril.laser.ethereum.plugins.plugin import LaserPlugin
from mythril.laser.ethereum.plugins.implementations.state_merge.merge_states import (
    merge_states,
)
from mythril.laser.ethereum.plugins.implementations.state_merge.check_mergeability import (
    check_ws_merge_condition,
)
from mythril.laser.ethereum.state.world_state import WorldState
import logging
from mythril.laser.ethereum.state.annotation import StateAnnotation

log = logging.getLogger(__name__)


class MergeAnnotation(StateAnnotation):
    pass


class StateMerge(LaserPlugin):
    """
    Tries to merge states based on their similarity.
    Currently it only tries to merge if everything is same
    except constraints and storage. And there is some tolerance level
    to the constraints.
    A state can be merged only once --> avoids segfaults + better performance
    """

    def initialize(self, symbolic_vm: LaserEVM):
        """Initializes the State merging plugin

        Introduces hooks for stop_sym_trans function
        :param symbolic_vm:
        :return:
        """

        @symbolic_vm.laser_hook("stop_sym_trans")
        def execute_stop_sym_trans_hook(svm: LaserEVM):

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
                merged_set = set()  # type: Set[int]
                for i, state in enumerate(old_states):
                    if i in merged_set:
                        continue
                    if len(list(state.get_annotations(MergeAnnotation))) > 0:
                        new_states.append(state)
                        continue
                    new_states.append(
                        self._look_for_merges(
                            i, old_states, merged_set
                        )
                    )

                old_states = copy(new_states)
            logging.info(
                "States reduced from {} to {}".format(num_old_states, len(new_states))
            )
            svm.open_states = new_states

    def _look_for_merges(
        self, offset: int, states: List[WorldState], merged_set: Set[int],
    ):
        """
        Tries to merge states[offset] with any of the states in states[offset+1:]
        :param offset: The offset of state
        :param states: The List of states
        :param merged_set: Set indicating which states are excluded from merging
        :return:
        """
        state = states[offset]
        for j in range(offset+1, len(states)):
            if j in merged_set or not self.check_merge_condition(
                state, states[j]
            ):
                j += 1
                continue
            merge_states(state, states[j])
            merged_set.add(j)
            state.annotations.append(MergeAnnotation())
            return state
        return state

    def check_merge_condition(self, state1: WorldState, state2: WorldState):
        """
        Check whether two world states can be merged
        :param state1:
        :param state2:
        :return: whether the states can be merged or not
        """
        basic_condition = check_ws_merge_condition(state1, state2)
        return basic_condition
