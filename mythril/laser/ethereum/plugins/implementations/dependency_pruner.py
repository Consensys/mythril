from mythril.laser.ethereum.svm import LaserEVM
from mythril.laser.ethereum.plugins.plugin import LaserPlugin
from mythril.laser.ethereum.plugins.signals import PluginSkipState
from mythril.laser.ethereum.state.annotation import StateAnnotation
from mythril.laser.ethereum.state.global_state import GlobalState
from mythril.laser.ethereum.transaction.transaction_models import (
    ContractCreationTransaction,
)
from typing import cast, List
from copy import copy
import logging

log = logging.getLogger(__name__)


class DependencyAnnotation(StateAnnotation):
    """Dependency Annotation

    This annotation tracks read and write access to the state.
    """

    def __init__(self):
        self.storage_loaded = []  # type: List
        self.storage_written = []  # type: List
        self.path = []  # type: List[int]

    def __copy__(self):
        result = DependencyAnnotation()
        result.storage_loaded = copy(self.storage_loaded)
        result.storage_written = copy(self.storage_written)
        result.path = copy(self.path)
        return result


def get_dependency_annotation(state: GlobalState) -> DependencyAnnotation:

    annotations = cast(
        List[DependencyAnnotation],
        list(state.world_state.get_annotations(DependencyAnnotation)),
    )
    if len(annotations) == 0:
        annotations = cast(
            List[DependencyAnnotation],
            list(state.get_annotations(DependencyAnnotation)),
        )

        if len(annotations) == 0:
            annotation = DependencyAnnotation()
            state.annotate(annotation)
        else:
            annotation = annotations[0]
    else:
        annotation = annotations[0]

    return annotation


class DependencyPruner(LaserPlugin):
    """Dependency Pruner Plugin
        For every basic block, this plugin keeps a list of storage locations that
        are accessed (read) in the subtree starting from that block. This map is built up over
        the whole symbolic execution run (i.e. new dependencies are added as they are
        discovered during later transactions).
        """

    def __init__(self):
        """Creates DependencyPruner"""
        self._reset()

    def _reset(self):
        self.iteration = 0
        self.dependency_map = {}  # type: Dict[int, List]
        pass

    def initialize(self, symbolic_vm: LaserEVM):
        """Initializes the DependencyPruner

        :param symbolic_vm
        """
        self._reset()

        @symbolic_vm.laser_hook("start_sym_trans")
        def start_sym_trans_hook():
            self.iteration += 1

        @symbolic_vm.pre_hook("JUMPDEST")
        def mutator_hook(state: GlobalState):
            """This method is where the actual pruning happens. If none of the storage locations previously written to
            is in the block's dependency map we skip the jump destination (pruning the path).

            :param state:
            :return:
            """
            annotation = get_dependency_annotation(state)
            address = state.get_current_instruction()["address"]

            annotation.path.append(state.get_current_instruction()["address"])

            if self.iteration < 2:
                return

            if address not in self.dependency_map:
                return

            if not set(annotation.storage_written).intersection(
                set(self.dependency_map[address])
            ):

                log.debug(
                    "Skipping state: Storage written: {} not in storage loaded: {}".format(
                        annotation.storage_written, self.dependency_map[address]
                    )
                )
                raise PluginSkipState

        @symbolic_vm.pre_hook("SSTORE")
        def mutator_hook(state: GlobalState):
            annotation = get_dependency_annotation(state)
            annotation.storage_written = list(
                set(annotation.storage_written + [state.mstate.stack[-1]])
            )

        @symbolic_vm.pre_hook("SLOAD")
        def mutator_hook(state: GlobalState):
            annotation = get_dependency_annotation(state)
            annotation.storage_loaded.append(state.mstate.stack[-1])

        @symbolic_vm.pre_hook("STOP")
        def mutator_hook(state: GlobalState):
            _transaction_end(state)

        @symbolic_vm.pre_hook("RETURN")
        def mutator_hook(state: GlobalState):
            _transaction_end(state)

        def _transaction_end(state: GlobalState):
            """When a stop or return is reached, the storage locations read along the path are entered into
            the dependency map for all nodes encountered in this path.

            :param state:
            :return:
            """

            annotation = get_dependency_annotation(state)

            for index in annotation.storage_loaded:

                for address in annotation.path:

                    if address in self.dependency_map:
                        self.dependency_map[address] = list(
                            set(self.dependency_map[address] + [index])
                        )
                    else:
                        self.dependency_map[address] = [index]

        @symbolic_vm.laser_hook("add_world_state")
        def world_state_filter_hook(state: GlobalState):

            if isinstance(state.current_transaction, ContractCreationTransaction):
                return

            annotation = get_dependency_annotation(state)
            state.world_state.annotate(annotation)

            log.debug(
                "Add World State {}\nDependency map: {}\nStorage indices written: {}".format(
                    state.get_current_instruction()["address"],
                    self.dependency_map,
                    annotation.storage_written,
                )
            )
