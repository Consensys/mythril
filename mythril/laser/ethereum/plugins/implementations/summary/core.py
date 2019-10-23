from mythril.laser.ethereum.svm import LaserEVM
from mythril.laser.ethereum.plugins.plugin import LaserPlugin
from mythril.laser.ethereum.state.annotation import StateAnnotation
from mythril.laser.ethereum.state.global_state import GlobalState
from mythril.laser.ethereum.state.account import Account
from mythril.laser.smt import K, Array, BaseArray, Bool

from typing import Dict, Tuple, List, Optional
from copy import copy

import logging

log = logging.getLogger(__name__)


class SummaryTrackingAnnotation(StateAnnotation):
    """ SummaryTrackingAnnotation
    This annotation is used by the symbolic summary plugin to keep track of data related to a summary that
    will be computed during the future exploration of the annotated world state.
    """

    def __init__(
        self,
        entry: GlobalState,
        storage_pairs: List[Tuple[BaseArray, BaseArray]],
        storage_constraints: List[Bool]
    ):
        self.entry = entry
        self.storage_pairs = storage_pairs
        self.storage_constraints = storage_constraints


class SymbolicSummary:
    """ Symbolic Summary

    A symbolic summary is an awesome construct that allows mythril to record and re-use partial analysis results
    """

    def __init__(
        self,
        storage_effect,
        condition,
        return_value,
        entry,
        exit,
    ):
        self.storage_effect = storage_effect
        self.condition = condition
        self.return_value = return_value
        self.entry = entry
        self.exit = exit


class SymbolicSummaryPlugin(LaserPlugin):

    def __init__(self):
        self.summaries = []

    def initialize(self, symbolic_vm: LaserEVM):
        """Initializes the symbolic summary generating plugin

        Introduces hooks for each instruction
        :param symbolic_vm: the symbolic virtual machine to initialize this plugin for
        """

        @symbolic_vm.laser_hook("stop_sym_exec")
        def stop_sym_exec_hook():
            # Print results
            log.info("Generated 0 summaries")

        @symbolic_vm.laser_hook("start_sym_trans")
        def execute_start_sym_trans_hook():
            pass

        @symbolic_vm.laser_hook("stop_sym_trans")
        def execute_stop_sym_trans_hook():
            pass

    def summary_entry(self, global_state: GlobalState):
        """ Handles logic for when the analysis reaches an entry point of a to-be recorded symbolic summary

        :param global_state: The state at the entry of the symbolic summary
        """
        storage_pairs = []
        storage_constraints = []

        for index, account in global_state.world_state.accounts.items():
            actual_storage = account.storage._standard_storage
            symbolic_storage = Array(f"{index}_symbolic_storage", 256, 256)
            account.storage._standard_storage = symbolic_storage
            storage_pairs.append((actual_storage, symbolic_storage))
            storage_constraints.append(actual_storage == symbolic_storage)

        summary_annotation = SummaryTrackingAnnotation(
            global_state,
            storage_pairs,
            storage_constraints
        )
        for constraint in storage_constraints:
            global_state.mstate.constraints.append(constraint)
        global_state.annotate(summary_annotation)

    def summary_exit(self, global_state: GlobalState):
        """ Handles logic for when the analysis reaches the summary exit

        This function populates self.summaries with the discovered symbolic summaries
        :param global_state: The state at the exit of the discovered symbolic summary
        """
        summary_annotation = self._get_and_remove_summary_tracking_annotation(global_state)
        if not summary_annotation:
            return

        self._record_symbolic_summary(global_state, summary_annotation)

        self._restore_previous_state(global_state, summary_annotation)

    @staticmethod
    def _get_and_remove_summary_tracking_annotation(global_state: GlobalState) -> Optional[SummaryTrackingAnnotation]:
        """ Retrieves symbolic summary from the global state"""
        summary_annotation: List[SummaryTrackingAnnotation] = list(
            global_state.get_annotations(SummaryTrackingAnnotation))
        if len(summary_annotation) != 1:
            logging.warning(
                f"Unexpected number of summary tracking annotations found: {len(summary_annotation)}\nSkipping..."
            )

        summary_annotation: SummaryTrackingAnnotation = summary_annotation[0]
        global_state.annotations.remove(summary_annotation)
        return summary_annotation

    def _record_symbolic_summary(self, global_state: GlobalState, tracking_annotation: SummaryTrackingAnnotation):
        """Records a summary between tracking_annotation.entry and global_state"""
        storage_mutations = []
        # TODO: record return value
        return_value = None

        for index, account in global_state.world_state.accounts.items():
            storage_mutations.append((index, account.storage._standard_storage))

        condition = global_state.mstate.constraints[:]
        for constraint in tracking_annotation.entry.mstate.constraints:
            condition.remove(constraint)

        summary = SymbolicSummary(
            storage_effect=storage_mutations,
            condition=condition,
            return_value=return_value,
            entry=tracking_annotation.entry.mstate.pc,
            exit=global_state.mstate.pc
        )
        self.summaries.append(summary)

    @staticmethod
    def _restore_previous_state(global_state: GlobalState, tracking_annotation: SummaryTrackingAnnotation):
        """Restores the previous persistent variables to the global state"""
        for account in global_state.world_state.accounts:
            for og_storage, sym_storage in tracking_annotation.storage_pairs:
                account.storage.replace(sym_storage, og_storage)
        for constraint in tracking_annotation.storage_constraints:
            global_state.mstate.constraints.remove(constraint)
