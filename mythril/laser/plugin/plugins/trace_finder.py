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
        self.tx_trace = []

    def initialize(self, symbolic_vm: LaserEVM):
        """Initializes the mutation pruner

        Introduces hooks for SSTORE operations
        :param symbolic_vm:
        :return:
        """
        self._reset()

        @symbolic_vm.laser_hook("start_exec")
        def start_sym_trans_hook():
            self.tx_trace.append([])

        @symbolic_vm.laser_hook("execute_state")
        def trace_jumpi_hook(global_state: GlobalState):
            self.tx_trace[-1].append(global_state.mstate.pc)
