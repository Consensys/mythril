from mythril.laser.ethereum.svm import LaserEVM
from mythril.laser.ethereum.plugins.plugin import LaserPlugin
from mythril.laser.ethereum.state.global_state import GlobalState

from typing import Dict, Tuple, List

import json
import logging

log = logging.getLogger(__name__)


BATCH_OF_STATES = 5


class CoveragePlugin(LaserPlugin):
    """InstructionCoveragePlugin

    This plugin measures the instruction coverage of mythril.
    The instruction coverage is the ratio between the instructions that have been executed
    and the total amount of instructions.

    Note that with lazy constraint solving enabled that this metric will be "unsound" as
    reachability will not be considered for the calculation of instruction coverage.

    """

    def __init__(self):
        self.instruction_coverage_data = {}  # type: Dict[str, Tuple[int, Dict[bool]]]
        self.branch_coverage_data = {}  # type: Dict[str, Dict[int, List]]
        self.tx_id = 0
        self.state_counter = 0
        self.coverage = []  # type: List[Dict[str, Dict[str, int]]]

    def initialize(self, symbolic_vm: LaserEVM):
        """Initializes the instruction coverage plugin

        Introduces hooks for each instruction
        :param symbolic_vm:
        :return:
        """
        self.instruction_coverage_data = {}
        self.branch_coverage_data = {}
        self.tx_id = 0

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

        @symbolic_vm.laser_hook("stop_sym_exec")
        def execute_stop_sym_exec_hook():
            self._calculate_branches()
            with open("data.json", "w") as outfile:
                json.dump(self.coverage, outfile)

    def _update_instruction_coverage_data(self, global_state: GlobalState):
        """
        Calculates instruction coverage
        :param global_state:
        :return:
        """
        code = global_state.environment.code.bytecode
        if code not in self.instruction_coverage_data.keys():
            number_of_instructions = len(global_state.environment.code.instruction_list)
            self.instruction_coverage_data[code] = (number_of_instructions, {})
        self.instruction_coverage_data[code][1][
            global_state.get_current_instruction()["address"]
        ] = True

    def _update_branch_coverage_data(self, global_state: GlobalState):
        code = global_state.environment.code.bytecode
        if code not in self.branch_coverage_data:
            self.branch_coverage_data[code] = {}
            for instruction in global_state.environment.code.instruction_list:
                if instruction["opcode"] != "JUMPI":
                    continue
                self.branch_coverage_data[code][instruction["address"]] = []

        if global_state.get_current_instruction()["opcode"] != "JUMPI":
            return
        addr = global_state.get_current_instruction()["address"]
        jump_addr = global_state.mstate.stack[-1]
        if jump_addr.symbolic:
            log.debug("Encountered a symbolic jump, ignoring it for branch coverage")
            return
        self.branch_coverage_data[code][addr] = [addr + 1, jump_addr]

    def _record_coverage(self):
        coverage = {}
        for code, code_cov in self.instruction_coverage_data.items():
            branches_covered = set()
            for jumps, branches in self.branch_coverage_data[code].items():
                for branch in branches:
                    if branch not in code_cov[1]:
                        continue
                    branches_covered.add(branch)
            coverage[code] = {
                "instructions_covered": len(code_cov[1]),
                "total_instructions": code_cov[0],
                "branches_covered": len(branches_covered),
                "tx_id": self.tx_id,
                "batch_of_states": BATCH_OF_STATES,
            }
            self.coverage.append(coverage)

    def _calculate_branches(self):
        for code, code_cov in self.instruction_coverage_data.items():
            total_branches = set()
            for jumps, branches in self.branch_coverage_data[code].items():
                for branch in branches:
                    total_branches.add(branch)
            for coverage in self.coverage:
                if code in coverage:
                    coverage[code]["total_branches"] = len(total_branches)
