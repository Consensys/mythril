from mythril.laser.plugin.interface import LaserPlugin
from mythril.laser.plugin.builder import PluginBuilder
from mythril.laser.ethereum.state.global_state import GlobalState
from mythril.laser.ethereum.svm import LaserEVM
from typing import List, Tuple


class TraceFinderBuilder(PluginBuilder):
    name = "trace-finder"
    plugin_default_enabled = True
    enabled = True

    author = "MythX Development Team"
    name = "MythX Trace Finder"
    plugin_license = "All rights reserved."
    plugin_type = "Laser Plugin"
    plugin_version = "0.0.1 "
    plugin_description = "This plugin merges states after the end of a transaction"

    def __call__(self, *args, **kwargs):
        return TraceFinder()


class TraceFinder(LaserPlugin):
    def __init__(self):
        self._reset()

    def _reset(self):
        self.tx_trace: List[List[Tuple[int, str]]] = []

    def initialize(self, symbolic_vm: LaserEVM):
        """Initializes Trace Finder

        Introduces hooks during the start of the execution and each execution state
        :param symbolic_vm:
        :return:
        """
        self._reset()

        @symbolic_vm.laser_hook("start_exec")
        def start_sym_trans_hook():
            self.tx_trace.append([])

        @symbolic_vm.laser_hook("execute_state")
        def trace_jumpi_hook(global_state: GlobalState):
            self.tx_trace[-1].append(
                (global_state.mstate.pc, global_state.current_transaction.id)
            )
