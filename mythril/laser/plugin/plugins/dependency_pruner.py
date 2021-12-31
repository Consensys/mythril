from mythril.laser.ethereum.svm import LaserEVM
from mythril.laser.plugin.interface import LaserPlugin
from mythril.laser.plugin.builder import PluginBuilder
from mythril.laser.plugin.signals import PluginSkipState
from mythril.laser.plugin.plugins.plugin_annotations import (
    DependencyAnnotation,
    WSDependencyAnnotation,
)
from mythril.laser.ethereum.state.global_state import GlobalState
from mythril.laser.ethereum.transaction.transaction_models import (
    ContractCreationTransaction,
)
from mythril.exceptions import UnsatError
from mythril.analysis import solver
from typing import cast, List, Dict, Set
import logging


log = logging.getLogger(__name__)


def get_dependency_annotation(state: GlobalState) -> DependencyAnnotation:
    """Returns a dependency annotation

    :param state: A global state object
    """

    annotations = cast(
        List[DependencyAnnotation], list(state.get_annotations(DependencyAnnotation))
    )

    if len(annotations) == 0:

        """FIXME: Hack for carrying over state annotations from the STOP and RETURN states of
        the previous states. The states are pushed on a stack in the world state annotation
        and popped off the stack in the subsequent iteration. This might break if any
        other strategy than bfs is used (?).
        """

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
    """Returns the world state annotation

    :param state: A global state object
    """

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


class DependencyPrunerBuilder(PluginBuilder):
    name = "dependency-pruner"

    def __call__(self, *args, **kwargs):
        return DependencyPruner()


class DependencyPruner(LaserPlugin):
    """Dependency Pruner Plugin

    For every basic block, this plugin keeps a list of storage locations that
    are accessed (read) in the execution path containing that block. This map
    is built up over the whole symbolic execution run.

    After the initial build up of the map in the first transaction, blocks are
    executed only if any of the storage locations written to in the previous
    transaction can have an effect on that block or any of its successors.
    """

    def __init__(self):
        """Creates DependencyPruner"""
        self._reset()

    def _reset(self):
        self.iteration = 0
        self.calls_on_path = {}  # type: Dict[int, bool]
        self.sloads_on_path = {}  # type: Dict[int, List[object]]
        self.sstores_on_path = {}  # type: Dict[int, List[object]]
        self.storage_accessed_global = set()  # type: Set

    def update_sloads(self, path: List[int], target_location: object) -> None:
        """Update the dependency map for the block offsets on the given path.

        :param path
        :param target_location
        """

        for address in path:
            if address in self.sloads_on_path:
                if target_location not in self.sloads_on_path[address]:
                    self.sloads_on_path[address].append(target_location)
            else:
                self.sloads_on_path[address] = [target_location]

    def update_sstores(self, path: List[int], target_location: object) -> None:
        """Update the dependency map for the block offsets on the given path.

        :param path
        :param target_location
        """

        for address in path:
            if address in self.sstores_on_path:
                if target_location not in self.sstores_on_path[address]:
                    self.sstores_on_path[address].append(target_location)
            else:
                self.sstores_on_path[address] = [target_location]

    def update_calls(self, path: List[int]) -> None:
        """Update the dependency map for the block offsets on the given path.

        :param path
        :param target_location
        """

        for address in path:
            if address in self.sstores_on_path:
                self.calls_on_path[address] = True

    def wanna_execute(self, address: int, annotation: DependencyAnnotation) -> bool:
        """Decide whether the basic block starting at 'address' should be executed.

        :param address
        :param storage_write_cache
        """

        storage_write_cache = annotation.get_storage_write_cache(self.iteration - 1)

        if address in self.calls_on_path:
            return True

        # Skip "pure" paths that don't have any dependencies.

        if address not in self.sloads_on_path:
            return False

        # Execute the path if there are state modifications along it that *could* be relevant

        if address in self.storage_accessed_global:
            for location in self.sstores_on_path:
                try:
                    solver.get_model((location == address,))
                    return True

                except UnsatError:
                    continue

        dependencies = self.sloads_on_path[address]

        # Execute the path if there's any dependency on state modified in the previous transaction

        for location in storage_write_cache:
            for dependency in dependencies:

                # Is there a known read operation along this path that matches a write in the previous transaction?

                try:
                    solver.get_model((location == dependency,))
                    return True

                except UnsatError:
                    continue

            # Has the *currently executed* path been influenced by a write operation in the previous transaction?

            for dependency in annotation.storage_loaded:
                try:
                    solver.get_model((location == dependency,))
                    return True
                except UnsatError:
                    continue

        return False

    def initialize(self, symbolic_vm: LaserEVM) -> None:
        """Initializes the DependencyPruner

        :param symbolic_vm
        """
        self._reset()

        @symbolic_vm.laser_hook("start_sym_trans")
        def start_sym_trans_hook():
            self.iteration += 1

        @symbolic_vm.post_hook("JUMP")
        def jump_hook(state: GlobalState):
            try:
                address = state.get_current_instruction()["address"]
            except IndexError:
                raise PluginSkipState
            annotation = get_dependency_annotation(state)
            annotation.path.append(address)

            _check_basic_block(address, annotation)

        @symbolic_vm.post_hook("JUMPI")
        def jumpi_hook(state: GlobalState):
            try:
                address = state.get_current_instruction()["address"]
            except IndexError:
                raise PluginSkipState
            annotation = get_dependency_annotation(state)
            annotation.path.append(address)

            _check_basic_block(address, annotation)

        @symbolic_vm.pre_hook("SSTORE")
        def sstore_hook(state: GlobalState):
            annotation = get_dependency_annotation(state)

            location = state.mstate.stack[-1]

            self.update_sstores(annotation.path, location)
            annotation.extend_storage_write_cache(self.iteration, location)

        @symbolic_vm.pre_hook("SLOAD")
        def sload_hook(state: GlobalState):
            annotation = get_dependency_annotation(state)
            location = state.mstate.stack[-1]

            if location not in annotation.storage_loaded:
                annotation.storage_loaded.add(location)

            # We backwards-annotate the path here as sometimes execution never reaches a stop or return
            # (and this may change in a future transaction).

            self.update_sloads(annotation.path, location)
            self.storage_accessed_global.add(location)

        @symbolic_vm.pre_hook("CALL")
        def call_hook(state: GlobalState):
            annotation = get_dependency_annotation(state)

            self.update_calls(annotation.path)
            annotation.has_call = True

        @symbolic_vm.pre_hook("STATICCALL")
        def staticcall_hook(state: GlobalState):
            annotation = get_dependency_annotation(state)

            self.update_calls(annotation.path)
            annotation.has_call = True

        @symbolic_vm.pre_hook("STOP")
        def stop_hook(state: GlobalState):
            _transaction_end(state)

        @symbolic_vm.pre_hook("RETURN")
        def return_hook(state: GlobalState):
            _transaction_end(state)

        def _transaction_end(state: GlobalState) -> None:
            """When a stop or return is reached, the storage locations read along the path are entered into
            the dependency map for all nodes encountered in this path.

            :param state:
            """

            annotation = get_dependency_annotation(state)

            for index in annotation.storage_loaded:
                self.update_sloads(annotation.path, index)

            for index in annotation.storage_written:
                self.update_sstores(annotation.path, index)

            if annotation.has_call:
                self.update_calls(annotation.path)

        def _check_basic_block(address: int, annotation: DependencyAnnotation):
            """This method is where the actual pruning happens.

            :param address: Start address (bytecode offset) of the block
            :param annotation:
            """

            # Don't skip any blocks in the contract creation transaction
            if self.iteration < 2:
                return

            # Don't skip newly discovered blocks
            if address not in annotation.blocks_seen:
                annotation.blocks_seen.add(address)
                return

            if self.wanna_execute(address, annotation):
                return
            else:
                log.debug(
                    "Skipping state: Storage slots {} not read in block at address {}, function".format(
                        annotation.get_storage_write_cache(self.iteration - 1), address
                    )
                )

                raise PluginSkipState

        @symbolic_vm.laser_hook("add_world_state")
        def world_state_filter_hook(state: GlobalState):

            if isinstance(state.current_transaction, ContractCreationTransaction):
                # Reset iteration variable
                self.iteration = 0
                return

            world_state_annotation = get_ws_dependency_annotation(state)
            annotation = get_dependency_annotation(state)

            # Reset the state annotation except for storage written which is carried on to
            # the next transaction

            annotation.path = [0]
            annotation.storage_loaded = set()

            world_state_annotation.annotations_stack.append(annotation)
