from mythril.laser.ethereum.strategy import BasicSearchStrategy
from mythril.laser.ethereum.state.global_state import GlobalState
from mythril.laser.plugin.plugins.coverage import InstructionCoveragePlugin


class CoverageStrategy(BasicSearchStrategy):
    """Implements a instruction coverage based search strategy

    This strategy is quite simple and effective, it prioritizes the execution of instructions that have previously been
    uncovered. Once there is no such global state left in the work list, it will resort to using the super_strategy.

    This strategy is intended to be used "on top of" another one
    """

    def __init__(
        self,
        super_strategy: BasicSearchStrategy,
        instruction_coverage_plugin: InstructionCoveragePlugin,
    ):
        self.super_strategy = super_strategy
        self.instruction_coverage_plugin = instruction_coverage_plugin
        BasicSearchStrategy.__init__(
            self, super_strategy.work_list, super_strategy.max_depth
        )

    def get_strategic_global_state(self) -> GlobalState:
        """
        Returns the first uncovered global state in the work list if it exists,
        otherwise super_strategy.get_strategic_global_state() is returned.
        """
        for global_state in self.work_list:
            if not self._is_covered(global_state):
                self.work_list.remove(global_state)
                return global_state
        return self.super_strategy.get_strategic_global_state()

    def _is_covered(self, global_state: GlobalState) -> bool:
        """Checks if the instruction for the given global state is already covered"""
        bytecode = global_state.environment.code.bytecode
        index = global_state.mstate.pc
        return self.instruction_coverage_plugin.is_instruction_covered(bytecode, index)
