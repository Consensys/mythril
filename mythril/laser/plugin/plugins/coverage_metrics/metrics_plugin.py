from mythril.laser.ethereum.svm import LaserEVM
from mythril.laser.plugin.interface import LaserPlugin
from mythril.laser.plugin.builder import PluginBuilder
from mythril.laser.ethereum.state.global_state import GlobalState
from .coverage_data import (
    CoverageTimeSeries,
    InstructionCoverageInfo,
)
from .constants import BATCH_OF_STATES
from typing import Dict, Tuple, List

import time
import logging

log = logging.getLogger(__name__)


class CoverageMetricsPluginBuilder(PluginBuilder):
    """CoveragePlugin
    Checks Instruction and branch coverage and puts it to data.json file
    which appears in the directory in which mythril is run.
    """

    plugin_default_enabled = True
    enabled = True

    author = "MythX Development Team"
    plugin_name = "MythX Coverage Metrics"
    plugin_license = "All rights reserved."
    plugin_type = "Laser Plugin"
    plugin_description = (
        "This plugin measures coverage throughout symbolic execution,"
        " reporting it at the end in the MythX coverage format."
    )

    def __call__(self, *args, **kwargs):
        """Constructs the plugin"""
        return LaserCoveragePlugin()


class LaserCoveragePlugin(LaserPlugin):
    def __init__(self):
        self.instruction_coverage_data = {}  # type: Dict[str, Tuple[int, Dict[bool]]]
        self.branch_possibilities = {}  # type: Dict[str, Dict[int, List]]
        self.tx_id = 0
        self.state_counter = 0
        self.coverage = CoverageTimeSeries()
        self.instruction_coverage_info = InstructionCoverageInfo()
        self.start_time = time.time_ns()

    def initialize(self, symbolic_vm: LaserEVM) -> None:
        """Initializes the instruction coverage plugin

        Introduces hooks for each instruction
        :param symbolic_vm: The symbolic virtual machine to initialise  this plugin for
        """
        log.info("Initializing coverage metrics plugin")

        self.instruction_coverage_data = {}
        self.branch_possibilities = {}
        self.tx_id = 0

        # Add the instruction coverage ExecutionInfo to laser vm for use in reporting
        symbolic_vm.execution_info.append(self.instruction_coverage_info)
        symbolic_vm.execution_info.append(self.coverage)

        @symbolic_vm.laser_hook("execute_state")
        def execute_state_hook(global_state: GlobalState):
            self._update_instruction_coverage_data(global_state)
            self._update_branch_coverage_data(global_state)
            self.state_counter += 1
            if self.state_counter == BATCH_OF_STATES:
                self._record_coverage()
                self.state_counter = 0

        @symbolic_vm.laser_hook("stop_sym_trans")
        def execute_stop_sym_trans_hook():
            self.tx_id += 1

        # The following is useful for debugging
        # @symbolic_vm.laser_hook("stop_sym_exec")
        # def execute_stop_sym_exec_hook():
        #     self.coverage.output("coverage_data.json")
        #     self.instruction_coverage_info.output("instruction_discovery_data.json")

    def _update_instruction_coverage_data(self, global_state: GlobalState):
        """Records instruction coverage"""
        code = global_state.environment.code.bytecode
        if code not in self.instruction_coverage_data.keys():
            number_of_instructions = len(global_state.environment.code.instruction_list)
            self.instruction_coverage_data[code] = (number_of_instructions, {})
        current_instr = global_state.get_current_instruction()["address"]
        if self.instruction_coverage_info.is_covered(code, current_instr) is False:
            self.instruction_coverage_info.add_data(
                code, current_instr, time.time_ns() - self.start_time
            )
        self.instruction_coverage_data[code][1][current_instr] = True

    def _update_branch_coverage_data(self, global_state: GlobalState):
        """Records branch coverage"""
        code = global_state.environment.code.bytecode
        if code not in self.branch_possibilities:
            self.branch_possibilities[code] = {}

        if global_state.get_current_instruction()["opcode"] != "JUMPI":
            return
        addr = global_state.get_current_instruction()["address"]
        jump_addr = global_state.mstate.stack[-1]
        if jump_addr.symbolic:
            log.debug("Encountered a symbolic jump, ignoring it for branch coverage")
            return
        self.branch_possibilities[code][addr] = [addr + 1, jump_addr.value]

    def _record_coverage(self):
        for code, code_cov in self.instruction_coverage_data.items():
            total_branches = 0
            branches_covered = 0
            for jumps, branches in self.branch_possibilities[code].items():
                for branch in branches:
                    total_branches += 1
                    branches_covered += branch in code_cov[1]
            self.coverage.add_data(
                code=code,
                instructions_covered=len(code_cov[1]),
                total_instructions=code_cov[0],
                branches_covered=branches_covered,
                tx_id=self.tx_id,
                total_branches=total_branches,
                state_counter=self.state_counter,
                time_elapsed=time.time_ns() - self.start_time,
            )
