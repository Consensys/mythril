from mythril.laser.ethereum.svm import LaserEVM
from mythril.laser.ethereum.plugins.plugin import LaserPlugin
from mythril.laser.smt import symbol_factory, simplify, Or
from mythril.laser.ethereum.state.world_state import WorldState
import logging
import z3

log = logging.getLogger(__name__)


class StateMerge(LaserPlugin):
    def initialize(self, symbolic_vm: LaserEVM):
        """Initializes the mutation pruner

        Introduces hooks for SSTORE operations
        :param symbolic_vm:
        :return:
        """

        @symbolic_vm.laser_hook("stop_sym_trans")
        def execute_stop_sym_trans_hook(svm: LaserEVM):
            log.info(svm.open_states)

            open_states = svm.open_states

            if len(open_states) == 0:
                return

            n_states = len(open_states) - 1
            new_states = []
            i = 0
            while i < n_states:
                if self.check_merge_condition(open_states[i], open_states[i + 1]):
                    new_states.append(
                        self.merge_states(open_states[i], open_states[i + 1])
                    )
                    i += 2
                    continue
                else:
                    new_states.append(open_states[i])
                if i == n_states - 1:
                    new_states.append(open_states[i - 1])
                i += 1
            logging.info(
                "States reduced from {} to {}".format(n_states + 1, len(new_states))
            )
            svm.open_states = new_states

    @staticmethod
    def check_merge_condition(state1: WorldState, state2: WorldState):
        # TODO: Use a better condition in the PR
        return state1.transaction_sequence == state2.transaction_sequence

    @staticmethod
    def merge_states(state1: WorldState, state2: WorldState) -> WorldState:
        state1.merge_states(state2)
        return state1
        # TODO Merge world state annotations

        # TODO Merge accounts
