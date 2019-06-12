from mythril.laser.ethereum.svm import LaserEVM
from mythril.laser.ethereum.plugins.plugin import LaserPlugin
from mythril.laser.ethereum.plugins.signals import PluginSkipState
from mythril.laser.ethereum.state.annotation import StateAnnotation
from mythril.laser.ethereum.state.global_state import GlobalState
from mythril.laser.ethereum.transaction.transaction_models import (
    ContractCreationTransaction,
)
from typing import cast, List, Set
from copy import copy
import logging

log = logging.getLogger(__name__)


class DependencyAnnotation(StateAnnotation):
    """Dependency Annotation

    This annotation tracks read and write access to the state.
    """

    def __init__(self):
        self.storage_loaded = set()  # type: Set
        self.storage_written = set()  # type: Set

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
    """

    def __init__(self):
        """Creates DependencyPruner"""

        """
        For every basic block, the dependency map keeps a list of storage locations that 
        might be read from any path starting from that block. This map is built up over
        the whole symbolic execution run (i.e. new dependencies are added if they are 
        discovered during later transactions).
        """

        self.dependency_map = {}  # type: Dict[int, List]

    def _reset(self):
        self.dependency_map = {}

    def initialize(self, symbolic_vm: LaserEVM):
        """Initializes the DependencyPruner

        :param symbolic_vm
        """
        self._reset()

        @symbolic_vm.pre_hook("JUMPDEST")
        def mutator_hook(state: GlobalState):
            annotation = get_dependency_annotation(state)
            address = state.get_current_instruction()["address"]

            annotation.path.append(state.get_current_instruction()["address"])

            if address not in self.dependency_map:
                # Blocks that don't have a dependency map yet are always executed.
                return

            """
            This is where the actual pruning happens. If none of the storage locations previously written to 
            is accessed in any node following the current node we skip the state.
            """

            if not annotation.storage_written.intersection(
                set(self.dependency_map[address])
            ):

                logging.debug(
                    "Skipping state: Storage written: {} not in storage loaded: {}".format(
                        annotation.storage_written, self.dependency_map[address]
                    )
                )
                raise PluginSkipState

        @symbolic_vm.pre_hook("SSTORE")
        def mutator_hook(state: GlobalState):
            annotation = get_dependency_annotation(state)
            annotation.storage_written.add(state.mstate.stack[-1])

        @symbolic_vm.pre_hook("SLOAD")
        def mutator_hook(state: GlobalState):

            annotation = get_dependency_annotation(state)
            annotation.storage_loaded.add(state.mstate.stack[-1])

        @symbolic_vm.pre_hook("STOP")
        def mutator_hook(state: GlobalState):
            annotation = get_dependency_annotation(state)

            for index in annotation.storage_loaded:

                for address in annotation.path:

                    if address in self.dependency_map:
                        self.dependency_map[address] = list(
                            set(self.dependency_map[address] + [index])
                        )
                    else:
                        self.dependency_map[address] = [index]

        @symbolic_vm.pre_hook("RETURN")
        def mutator_hook(state: GlobalState):
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
                "Adding new world state {} with dependency map:\n{}\nStorage indices written: {}".format(
                    state.get_current_instruction()["address"],
                    self.dependency_map,
                    annotation.storage_written,
                )
            )
