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
    def __init__():
        pass


class SymbolicSummary:
    """ Symbolic Summary

    A symbolic summary is an awesome construct that allows mythril to record and re-use partial analysis results
    """
    def __init__():
        pass


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
        pass
