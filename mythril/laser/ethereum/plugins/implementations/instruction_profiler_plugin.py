from mythril.laser.ethereum.svm import LaserEVM
from mythril.laser.ethereum.plugins.plugin import LaserPlugin
from mythril.laser.ethereum.state.global_state import GlobalState


class InstructionProfilerPlugin(LaserPlugin):
    """ Instruction profiler plugin

    This plugin implements the logic that profiles the execution for the different instructions
    It does so by measuring the frequency and duration of each operation execution
    """

    def initialize(self, symbolic_vm: LaserEVM):
        """Initializes the instruction profiler

        Introduces hooks that measure the duration of each execution and the name of the instruction being executed
        :param symbolic_vm: The virtual machine to initialize the plugin for
        """
        pass
