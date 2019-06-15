from mythril.laser.ethereum.svm import LaserEVM
from mythril.laser.ethereum.plugins.plugin import LaserPlugin
from mythril.laser.ethereum.plugins.signals import PluginSkipState
from mythril.laser.ethereum.state.annotation import StateAnnotation
from mythril.laser.ethereum.state.global_state import GlobalState
from mythril.laser.ethereum.transaction.transaction_models import (
    ContractCreationTransaction,
)
from mythril.exceptions import UnsatError
from mythril.analysis import solver
from typing import cast, List, Dict
from copy import copy
import logging


log = logging.getLogger(__name__)


class DependencyAnnotation(StateAnnotation):
    """Dependency Annotation

    This annotation tracks read and write access to the state during each transaction.
    """

    def __init__(self):
        self.storage_loaded = []  # type: List
        self.storage_written = {}  # type: Dict[int, List]
        self.has_call = False
        self.path = [0]  # type: List

    def __copy__(self):
        result = DependencyAnnotation()
        result.storage_loaded = copy(self.storage_loaded)
        result.storage_written = copy(self.storage_written)
        result.path = copy(self.path)
        return result

    def get_storage_write_cache(self, iteration: int):
        if iteration not in self.storage_written:
            self.storage_written[iteration] = []

        return self.storage_written[iteration]

    def extend_storage_write_cache(self, iteration: int, value: object):
        if iteration not in self.storage_written:
            self.storage_written[iteration] = [value]
        else:
            if value not in self.storage_written[iteration]:
                self.storage_written[iteration].append(value)


class WSDependencyAnnotation(StateAnnotation):
    """Dependency Annotation for World state

    This  world state annotation maintains a stack of state annotations.
    It is used to transfer individual state annotations from one transaction to the next.
    """

    def __init__(self):
        self.annotations_stack = []

    def __copy__(self):
        result = WSDependencyAnnotation()
        result.annotations_stack = copy(self.annotations_stack)
        return result


def get_dependency_annotation(state: GlobalState) -> DependencyAnnotation:
    """ Returns a dependency annotation

    :param state: A global state object
    """

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
    """ Returns the world state annotation

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


class DependencyPruner(LaserPlugin):
    """Dependency Pruner Plugin

        For every basic block, this plugin keeps a list of storage locations that
        are accessed (read) in the execution path containing that block's. This map
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
        self.dependency_map = {}  # type: Dict[int, List[object]]
        self.protected_addresses = {}  # type: Set[int]

    def update_dependency_map(self, path: [int], target_location: object) -> None:
        """Update the dependency map for the block offsets on the given path.

        :param path
        :param target_location
        """

        for address in path:

            if address in self.dependency_map:
                if target_location not in self.dependency_map[address]:
                    self.dependency_map[address].append(target_location)
            else:
                self.dependency_map[address] = [target_location]

    def protect_path(self, path: [int]) -> None:
        """Prevent an execution path of being pruned.

        :param path
        """

        for address in path:
            self.protected_addresses.add(address)

    def wanna_execute(self, address: int, storage_write_cache) -> bool:
        """Decide whether the basic block starting at 'address' should be executed.

        :param address
        :param storage_write_cache
        """

        if address in self.protected_addresses or address not in self.dependency_map:
            return True

        dependencies = self.dependency_map[address]

        # Return if *any* dependency is found

        for location in storage_write_cache:
            for dependency in dependencies:

                try:
                    solver.get_model([location == dependency])
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

        @symbolic_vm.post_hook("CALL")
        def mutator_hook(state: GlobalState):
            annotation = get_dependency_annotation(state)

            annotation.has_call = True
            self.protect_path(annotation.path)

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

        def _check_basic_block(address: int, annotation: DependencyAnnotation):
            """This method is where the actual pruning happens.

             :param address: Start address (bytecode offset) of the block
             :param annotation
             """

            if self.iteration < 1:
                return

            annotation.path.append(address)

            if self.wanna_execute(
                address, annotation.get_storage_write_cache(self.iteration - 1)
            ):
                return
            else:
                log.debug(
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
            location = state.mstate.stack[-1]

            if location not in annotation.storage_loaded:
                annotation.storage_loaded.append(location)

            # We backwards-annotate the path here as sometimes execution never reaches a stop or return
            # (and this may change in a future transaction).

            self.update_dependency_map(annotation.path, location)

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

            if annotation.has_call:
                self.protect_path(annotation.path)

            for index in annotation.storage_loaded:
                self.update_dependency_map(annotation.path, index)

        @symbolic_vm.laser_hook("add_world_state")
        def world_state_filter_hook(state: GlobalState):

            if isinstance(state.current_transaction, ContractCreationTransaction):
                return

            world_state_annotation = get_ws_dependency_annotation(state)
            annotation = get_dependency_annotation(state)

            # Reset the state annotation except for storage written which is carried on to
            # the next transaction

            annotation.path = [0]
            annotation.storage_loaded = []
            annotation.has_call = False

            world_state_annotation.annotations_stack.append(annotation)

            log.debug(
                "Iteration {}: Adding world state at address {}, end of function {}.\nDependency map: {}\nStorage written: {}".format(
                    self.iteration,
                    state.get_current_instruction()["address"],
                    state.node.function_name,
                    self.dependency_map,
                    annotation.storage_written[self.iteration],
                )
            )
