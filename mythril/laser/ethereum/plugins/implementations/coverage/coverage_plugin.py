from mythril.laser.ethereum.svm import LaserEVM
from mythril.laser.ethereum.plugins.plugin import LaserPlugin
from mythril.laser.ethereum.state.global_state import GlobalState

from typing import Dict, Tuple, List

import logging

log = logging.getLogger(__name__)


class InstructionCoveragePlugin(LaserPlugin):
    """InstructionCoveragePlugin

    This plugin measures the instruction coverage of mythril.
    The instruction coverage is the ratio between the instructions that have been executed
    and the total amount of instructions.

    Note that with lazy constraint solving enabled that this metric will be "unsound" as
    reachability will not be considered for the calculation of instruction coverage.

    """

    def __init__(self):
        self.coverage = {}  # type: Dict[str, Tuple[int, List[bool]]]
        self.initial_coverage = 0
        self.tx_id = 0

    def initialize(self, symbolic_vm: LaserEVM):
        """Initializes the instruction coverage plugin

        Introduces hooks for each instruction
        :param symbolic_vm:
        :return:
        """
        self.coverage = {}
        self.initial_coverage = 0
        self.tx_id = 0

        @symbolic_vm.laser_hook("stop_sym_exec")
        def stop_sym_exec_hook():
            # Print results
            for code, code_cov in self.coverage.items():
                cov_percentage = sum(code_cov[1]) / float(code_cov[0]) * 100

                log.info(
                    "Achieved {:.2f}% coverage for code: {}".format(
                        cov_percentage, code
                    )
                )

        @symbolic_vm.laser_hook("execute_state")
        def execute_state_hook(global_state: GlobalState):
            # Record coverage
            code = global_state.environment.code.bytecode

            if code not in self.coverage.keys():
                number_of_instructions = len(
                    global_state.environment.code.instruction_list
                )
                self.coverage[code] = (
                    number_of_instructions,
                    [False] * number_of_instructions,
                )

            self.coverage[code][1][global_state.mstate.pc] = True

        @symbolic_vm.laser_hook("start_sym_trans")
        def execute_start_sym_trans_hook():
            self.initial_coverage = self._get_covered_instructions()

        @symbolic_vm.laser_hook("stop_sym_trans")
        def execute_stop_sym_trans_hook(svm: LaserEVM):
            end_coverage = self._get_covered_instructions()
            log.info(
                "Number of new instructions covered in tx %d: %d"
                % (self.tx_id, end_coverage - self.initial_coverage)
            )
            self.tx_id += 1

    def _get_covered_instructions(self) -> int:
        """Gets the total number of covered instructions for all accounts in
        the svm.
        :return:
        """
        total_covered_instructions = 0
        for _, cv in self.coverage.items():
            total_covered_instructions += sum(cv[1])
        return total_covered_instructions

    def is_instruction_covered(self, bytecode, index):
        if bytecode not in self.coverage.keys():
            return False

        try:
            return self.coverage[bytecode][index]
        except IndexError:
            return False
