from typing import List
from mythril.laser.ethereum.svm import LaserEVM
from mythril.laser.ethereum.plugins.signals import PluginSkipState
from mythril.laser.ethereum.plugins.plugin import LaserPlugin
from mythril.laser.ethereum.state.global_state import GlobalState


class FunctionSelector(LaserPlugin):
    """Function selector plugin

    Lets the user specify a whitelist or blacklist of function signatures.
    If the whitelist is non-empty then only functions contained in it are executed.
    Otherwise, all functions are executed unless they are in the blacklist.


    """

    def __init__(self, _whitelist: List[str] = [], _blacklist: List[str] = []):
        """Initializes the plugin

        :param _whitelist: List of functions to be executed
        :param _blacklist: List of functions to be skipped
        """

        self.whitelist = _whitelist
        self.blacklist = _blacklist

    def initialize(self, symbolic_vm: LaserEVM):
        """Introduces a hook for adding a new state to the work list

        :param symbolic_vm:
        :return:
        """

        @symbolic_vm.laser_hook("execute_state")
        def world_state_filter_hook(global_state: GlobalState):
            if (
                len(self.whitelist)
                and global_state.node.function_name not in self.whitelist
            ):
                raise PluginSkipState

            if global_state.node.function_name in self.blacklist:
                raise PluginSkipState
