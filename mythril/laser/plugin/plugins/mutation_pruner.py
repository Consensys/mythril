from mythril.laser.plugin.signals import PluginSkipWorldState
from mythril.laser.plugin.interface import LaserPlugin
from mythril.laser.plugin.builder import PluginBuilder
from mythril.laser.plugin.plugins.plugin_annotations import MutationAnnotation
from mythril.laser.ethereum.state.global_state import GlobalState
from mythril.laser.ethereum.svm import LaserEVM
from mythril.laser.smt import UGT, symbol_factory
from mythril.laser.ethereum.transaction.transaction_models import (
    ContractCreationTransaction,
)
from mythril.analysis import solver
from mythril.exceptions import UnsatError


class MutationPrunerBuilder(PluginBuilder):
    name = "mutation-pruner"

    def __call__(self, *args, **kwargs):
        return MutationPruner()


class MutationPruner(LaserPlugin):
    """Mutation pruner plugin

    Let S be a world state from which T is a symbolic transaction, and S' is the resulting world state.
    In a situation where T does not execute any mutating instructions we can safely abandon further analysis on top of
    state S'. This is for the reason that we already performed analysis on S, which is equivalent.

    This optimization inhibits path explosion caused by "clean" behaviour

    The basic operation of this plugin is as follows:
     - Hook all mutating operations and introduce a MutationAnnotation to the global state on execution of the hook
     - Hook the svm EndTransaction on execution filter the states that do not have a mutation annotation

    """

    def initialize(self, symbolic_vm: LaserEVM):
        """Initializes the mutation pruner

        Introduces hooks for SSTORE operations
        :param symbolic_vm:
        :return:
        """

        @symbolic_vm.pre_hook("SSTORE")
        def sstore_mutator_hook(global_state: GlobalState):
            global_state.annotate(MutationAnnotation())

        """FIXME: Check for changes in world_state.balances instead of adding MutationAnnotation for all calls.
           Requires world_state.starting_balances to be initalized at every tx start *after* call value has been added.
        """

        @symbolic_vm.pre_hook("CALL")
        def call_mutator_hook(global_state: GlobalState):
            global_state.annotate(MutationAnnotation())

        @symbolic_vm.pre_hook("STATICCALL")
        def staticcall_mutator_hook(global_state: GlobalState):
            global_state.annotate(MutationAnnotation())

        @symbolic_vm.laser_hook("add_world_state")
        def world_state_filter_hook(global_state: GlobalState):

            if isinstance(
                global_state.current_transaction, ContractCreationTransaction
            ):
                return

            if isinstance(global_state.environment.callvalue, int):
                callvalue = symbol_factory.BitVecVal(
                    global_state.environment.callvalue, 256
                )
            else:
                callvalue = global_state.environment.callvalue

            try:

                constraints = global_state.world_state.constraints + [
                    UGT(callvalue, symbol_factory.BitVecVal(0, 256))
                ]

                solver.get_model(constraints)
                return
            except UnsatError:
                # callvalue is constrained to 0, therefore there is no balance based world state mutation
                pass

            if len(list(global_state.get_annotations(MutationAnnotation))) == 0:
                raise PluginSkipWorldState
