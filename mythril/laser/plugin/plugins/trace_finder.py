from mythril.laser.plugin.signals import PluginSkipWorldState
from mythril.laser.plugin.interface import LaserPlugin
from mythril.laser.plugin.builder import PluginBuilder
from mythril.laser.plugin.plugins.plugin_annotations import MutationAnnotation
from mythril.laser.ethereum.state.global_state import GlobalState
from mythril.laser.ethereum.svm import LaserEVM
from mythril.laser.smt import UGT, symbol_factory, simplify, Bool
from mythril.laser.ethereum.transaction.transaction_models import (
    ContractCreationTransaction,
)
from mythril.analysis import solver
from mythril.exceptions import UnsatError


class TraceFinderBuilder(PluginBuilder):
    name = "trace-finder"

    def __call__(self, *args, **kwargs):
        return TraceFinder()


class TraceFinder(LaserPlugin):
    def __init__(self):
        self._reset()

    def _reset(self):
        self.tx_trace = {}
        self.iteration = 0

    def initialize(self, symbolic_vm: LaserEVM):
        """Initializes the mutation pruner

        Introduces hooks for SSTORE operations
        :param symbolic_vm:
        :return:
        """
        self._reset()

        @symbolic_vm.laser_hook("start_sym_trans")
        def start_sym_trans_hook():
            self.iteration += 1

        @symbolic_vm.pre_hook("JUMPI")
        def trace_jumpi_hook(global_state: GlobalState):
            condition = global_state.mstate.stack[-2]
            condition = (
                simplify(condition) if isinstance(condition, Bool) else condition != 0
            )
            self.tx_trace[self.iteration].append(condition)
