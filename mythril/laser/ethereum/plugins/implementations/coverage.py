from mythril.laser.ethereum.svm import LaserEVM
from mythril.laser.ethereum.plugins.plugin import LaserPlugin
from mythril.laser.ethereum.state.global_state import GlobalState

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

    def initialize(self, symbolic_vm: LaserEVM):
        """Initializes the instruction coverage plugin

        Introduces hooks for each instruction
        :param symbolic_vm:
        :return:
        """
        coverage = {}

        @symbolic_vm.laser_hook("stop_sym_exec")
        def stop_sym_exec_hook():
            # Print results
            for code, code_cov in coverage.items():
                cov_percentage = sum(code_cov[1]) / float(code_cov[0]) * 100

                log.info("Achieved {:.2f}% coverage for code: {}".format(cov_percentage, code))

        @symbolic_vm.laser_hook("execute_state")
        def execute_state_hook(global_state: GlobalState):
            # Record coverage
            code = global_state.environment.code.bytecode

            if code not in coverage.keys():
                number_of_instructions = len(global_state.environment.code.instruction_list)
                coverage[code] = (
                    number_of_instructions,
                    [False] * number_of_instructions,
                )

            coverage[code][1][global_state.mstate.pc] = True
