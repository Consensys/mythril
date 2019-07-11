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

            merged_state = open_states[0]
            n_states = len(open_states) - 1

            for i in range(0, n_states):

                other_state = open_states.pop(-1)
                self.merge_states(merged_state, 0, other_state, i)

    @staticmethod
    def merge_states(state1: WorldState, i1, state2: WorldState, i2):

        ws_id = symbol_factory.BitVecSym("ws_id", 256)

        state1.node.constraints = [
            simplify(
                (state1.node.constraints and ws_id == i1)
                or (state2.node.constraints and ws_id == i2)
            )
        ]

        # TODO Merge world state annotations

        # TODO Merge accounts
