from mythril.laser.ethereum.svm import LaserEVM
from mythril.laser.ethereum.plugins.plugin import LaserPlugin
from mythril.laser.ethereum.plugins.signals import PluginSkipState
from mythril.laser.ethereum.state.annotation import StateAnnotation
from mythril.laser.ethereum.state.global_state import GlobalState
from mythril.laser.ethereum.util import get_concrete_int
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
        self.storage_written = {}  # type: Dict[int, List]
        self.path = [0]  # type: List

    def __copy__(self):
        result = DependencyAnnotation()
        result.storage_loaded = copy(self.storage_loaded)
        result.storage_written = copy(self.storage_written)
        result.path = copy(self.path)
        return result

    def get_storage_write_cache(self, iteration):
        if iteration not in self.storage_written:
            self.storage_written[iteration] = []

        return self.storage_written[iteration]

    def extend_storage_write_cache(self, iteration, value):
        if iteration not in self.storage_written:
            self.storage_written[iteration] = [value]
        else:
            self.storage_written[iteration] = list(
                set(self.storage_written[iteration] + [value])
            )


class WSDependencyAnnotation(StateAnnotation):
    """Dependency Annotation for World state

    This annotation tracks read and write access to the state.
    """

    def __init__(self):
        self.annotations_stack = []

    def __copy__(self):
        result = WSDependencyAnnotation()
        result.annotations_stack = copy(self.annotations_stack)
        return result


def get_dependency_annotation(state: GlobalState) -> DependencyAnnotation:

    annotations = cast(
        List[DependencyAnnotation], list(state.get_annotations(DependencyAnnotation))
    )

    if len(annotations) == 0:

        try:
            world_state_annotation = get_ws_dependency_annotation(state)
            annotation = world_state_annotation.annotations_stack.pop()
        except IndexError:
            annotation = DependencyAnnotation()

        state.annotate(annotation)
    else:
        annotation = annotations[0]

    return annotation


def get_ws_dependency_annotation(state: GlobalState) -> WSDependencyAnnotation:

    annotations = cast(
        List[WSDependencyAnnotation],
        list(state.world_state.get_annotations(WSDependencyAnnotation)),
    )

    if len(annotations) == 0:
        annotation = WSDependencyAnnotation()
        state.world_state.annotate(annotation)
    else:
        annotation = annotations[0]

    return annotation


class DependencyPruner(LaserPlugin):
    """Dependency Pruner Plugin
        For every basic block, this plugin keeps a list of storage locations that
        are accessed (read) in the subtree starting from that block. This map is built up over
        the whole symbolic execution run.
        """

    def __init__(self):
        """Creates DependencyPruner"""
        self._reset()

    def _reset(self):
        self.iteration = 0
        self.dependency_map = {}  # type: Dict[int, List]

    def initialize(self, symbolic_vm: LaserEVM):
        """Initializes the DependencyPruner

        :param symbolic_vm
        """
        self._reset()

        @symbolic_vm.laser_hook("start_sym_trans")
        def start_sym_trans_hook():
            self.iteration += 1

        @symbolic_vm.post_hook("JUMP")
        def mutator_hook(state: GlobalState):
            address = state.get_current_instruction()["address"]
            annotation = get_dependency_annotation(state)

            _check_basic_block(address, annotation)

        @symbolic_vm.pre_hook("JUMPDEST")
        def mutator_hook(state: GlobalState):
            address = state.get_current_instruction()["address"]
            annotation = get_dependency_annotation(state)

            _check_basic_block(address, annotation)

        @symbolic_vm.post_hook("JUMPI")
        def mutator_hook(state: GlobalState):
            address = state.get_current_instruction()["address"]
            annotation = get_dependency_annotation(state)

            _check_basic_block(address, annotation)

        def _check_basic_block(address, annotation):
            """This method is where the actual pruning happens. If none of the storage locations previously written to
             is in the block's dependency map we skip the jump destination (pruning the path).

             :param state:
             :return:
             """

            if self.iteration < 2:
                # Contract creation and build initial dependency map
                return

            annotation.path.append(address)

            if address not in self.dependency_map:
                return

            if not set(
                annotation.get_storage_write_cache(self.iteration - 1)
            ).intersection(set(self.dependency_map[address])):
                log.info(
                    "Skipping state: Storage slots {} not read in block at address {}".format(
                        annotation.get_storage_write_cache(self.iteration - 1), address
                    )
                )
                raise PluginSkipState

        @symbolic_vm.pre_hook("SSTORE")
        def sstore_hook(state: GlobalState):
            annotation = get_dependency_annotation(state)

            annotation.extend_storage_write_cache(
                self.iteration, state.mstate.stack[-1]
            )

        @symbolic_vm.pre_hook("SLOAD")
        def sload_hook(state: GlobalState):
            annotation = get_dependency_annotation(state)
            annotation.storage_loaded = list(
                set(annotation.storage_loaded + [state.mstate.stack[-1]])
            )

        @symbolic_vm.pre_hook("STOP")
        def stop_hook(state: GlobalState):
            _transaction_end(state)

        @symbolic_vm.pre_hook("RETURN")
        def return_hook(state: GlobalState):
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

            world_state_annotation = get_ws_dependency_annotation(state)
            annotation = get_dependency_annotation(state)
            annotation.path = [0]
            annotation.storage_loaded = []
            world_state_annotation.annotations_stack.append(annotation)

            log.debug(
                "Iteration {}: Add World State {}\nDependency map: {}\n".format(
                    self.iteration,
                    state.get_current_instruction()["address"],
                    self.dependency_map,
                    annotation.storage_written[self.iteration],
                )
            )
