from copy import copy
from typing import Set, List
from mythril.laser.ethereum.svm import LaserEVM
from mythril.laser.plugin.interface import LaserPlugin
from .merge_states import merge_states
from .check_mergeability import check_ws_merge_condition
from mythril.laser.ethereum.state.world_state import WorldState
from mythril.laser.ethereum.state.annotation import StateAnnotation
from mythril.laser.plugin.interface import LaserPlugin
import logging

log = logging.getLogger(__name__)


class MergeAnnotation(StateAnnotation):
    pass


class StateMergePluginBuilder(LaserPlugin):
    plugin_default_enabled = True
    enabled = True

    author = "MythX Development Team"
    name = "MythX State Merge"
    plugin_license = "All rights reserved."
    plugin_type = "Laser Plugin"
    plugin_version = "0.0.1 "
    plugin_description = "This plugin merges states after the end of a transaction"

    def __call__(self, *args, **kwargs):
        return StateMergePlugin()


class StateMergePlugin(LaserPlugin):
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
        def execute_stop_sym_trans_hook():
            open_states = symbolic_vm.open_states
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
                    new_states.append(self._look_for_merges(i, old_states, merged_set))

                old_states = copy(new_states)
            log.info(f"States reduced from {num_old_states} to {len(new_states)}")
            symbolic_vm.open_states = new_states

    def _look_for_merges(
        self,
        offset: int,
        states: List[WorldState],
        merged_set: Set[int],
    ) -> WorldState:
        """
        Tries to merge states[offset] with any of the states in states[offset+1:]
        :param offset: The offset of state
        :param states: The List of states
        :param merged_set: Set indicating which states are excluded from merging
        :return: Returns a state
        """
        state = states[offset]
        for j in range(offset + 1, len(states)):
            if j in merged_set or not check_ws_merge_condition(state, states[j]):
                continue
            merge_states(state, states[j])
            merged_set.add(j)
            state.annotations.append(MergeAnnotation())
            return state
        return state
