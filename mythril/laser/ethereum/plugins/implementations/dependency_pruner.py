from mythril.laser.ethereum.svm import LaserEVM
from mythril.laser.ethereum.plugins.plugin import LaserPlugin
from mythril.laser.ethereum.plugins.signals import PluginSkipWorldState
from mythril.laser.ethereum.state.annotation import StateAnnotation
from mythril.laser.ethereum.state.global_state import GlobalState
from mythril.laser.ethereum.util import get_concrete_int
from copy import copy


class PathAnnotation(StateAnnotation):
    """Dependency Annotation

    This is the annotation used to annotate paths
    """

    def __init__(self):
        self.path = []

    def __copy__(self):
        result = PathAnnotation()
        result.path = copy(self.path)
        return result


class DependencyPruner(LaserPlugin):
    """Dependency Pruner Plugin
    """

    def __init__(self):
        """Creates DependencyPruner"""
        pass

    def _reset(self):
        """Reset this plugin"""
        pass

    def initialize(self, symbolic_vm: LaserEVM):
        """Initializes the DependencyPruner

        Introduces hooks in symbolic_vm to track the desired values
        :param symbolic_vm
        """
        self._reset()

        @symbolic_vm.laser_hook("start_sym_trans")
        def start_sym_exec_hook():
            pass

        @symbolic_vm.laser_hook("stop_sym_trans")
        def stop_sym_exec_hook():
            pass

        @symbolic_vm.pre_hook("JUMPDEST")
        def mutator_hook(global_state: GlobalState):
            pass

        @symbolic_vm.pre_hook("SSTORE")
        def mutator_hook(global_state: GlobalState):
            pass

        @symbolic_vm.pre_hook("STOP")
        def mutator_hook(global_state: GlobalState):
            pass

        @symbolic_vm.laser_hook("add_world_state")
        def world_state_filter_hook(global_state: GlobalState):
            # raise PluginSkipWorldState
            pass
