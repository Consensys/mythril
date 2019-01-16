from mythril.laser.ethereum.state.annotation import StateAnnotation
from mythril.laser.ethereum.svm import LaserEVM
from mythril.laser.ethereum.plugins.signals import PluginSkipWorldState
from mythril.laser.ethereum.state.global_state import GlobalState
from mythril.laser.ethereum.transaction.transaction_models import (
    MessageCallTransaction,
)


class MutationAnnotation(StateAnnotation):
    """Mutation Annotation

    This is the annotation used by the MutationPruner plugin to record mutations
    """

    pass


class MutationPruner:
    """Mutation pruner plugin

    Let S be a world state from which T is a symbolic transaction, and S' is the resulting world state.
    In a situation where T does not execute any mutating instructions we can safely abandon further analysis on top of
    state S'. This is for the reason that we already performed analysis on S, which is equivalent.

    This optimization inhibits path explosion caused by "clean" behaviour

    The basic operation of this plugin is as follows:
     - Hook all mutating operations and introduce a MutationAnnotation to the global state on execution of the hook
     - Hook the svm EndTransaction on execution filter the states that do not have a mutation annotation

    """

    def __init__(self):
        pass

    def initialize(self, symbolic_vm: LaserEVM):
        """Initializes the mutation pruner

        Introduces hooks for SSTORE operations
        :param symbolic_vm:
        :return:
        """

        @symbolic_vm.pre_hook("SSTORE")
        def mutator_hook(global_state: GlobalState):
            global_state.annotate(MutationAnnotation())

        @symbolic_vm.laser_hook("add_world_state")
        def world_state_filter_hook(global_state: GlobalState):
            if isinstance(global_state.current_transaction, MessageCallTransaction) and len(list(global_state.get_annotations(MutationAnnotation))) == 0:
                    raise PluginSkipWorldState
