"""This module contains a representation of the global execution state."""
from typing import Dict, Union, List, Iterable, TYPE_CHECKING

from copy import copy, deepcopy
from z3 import BitVec

from mythril.laser.smt import symbol_factory
from mythril.laser.ethereum.cfg import Node
from mythril.laser.ethereum.state.environment import Environment
from mythril.laser.ethereum.state.machine_state import MachineState
from mythril.laser.ethereum.state.annotation import StateAnnotation

if TYPE_CHECKING:
    from mythril.laser.ethereum.state.world_state import WorldState
    from mythril.laser.ethereum.transaction.transaction_models import (
        MessageCallTransaction,
        ContractCreationTransaction,
    )


class GlobalState:
    """GlobalState represents the current globalstate."""

    def __init__(
        self,
        world_state: "WorldState",
        environment: Environment,
        node: Node,
        machine_state=None,
        transaction_stack=None,
        last_return_data=None,
        annotations=None,
    ) -> None:
        """Constructor for GlobalState.

        :param world_state:
        :param environment:
        :param node:
        :param machine_state:
        :param transaction_stack:
        :param last_return_data:
        :param annotations:
        """
        self.node = node
        self.world_state = world_state
        self.environment = environment
        self.mstate = (
            machine_state if machine_state else MachineState(gas_limit=1000000000)
        )
        self.transaction_stack = transaction_stack if transaction_stack else []
        self.op_code = ""
        self.last_return_data = last_return_data
        self._annotations = annotations or []

    def __copy__(self) -> "GlobalState":
        """

        :return:
        """
        world_state = copy(self.world_state)
        environment = copy(self.environment)
        mstate = deepcopy(self.mstate)
        transaction_stack = copy(self.transaction_stack)
        return GlobalState(
            world_state,
            environment,
            self.node,
            mstate,
            transaction_stack=transaction_stack,
            last_return_data=self.last_return_data,
            annotations=[copy(a) for a in self._annotations],
        )

    @property
    def accounts(self) -> Dict:
        """

        :return:
        """
        return self.world_state._accounts

    # TODO: remove this, as two instructions are confusing
    def get_current_instruction(self) -> Dict:
        """Gets the current instruction for this GlobalState.

        :return:
        """

        instructions = self.environment.code.instruction_list
        return instructions[self.mstate.pc]

    @property
    def current_transaction(
        self
    ) -> Union["MessageCallTransaction", "ContractCreationTransaction", None]:
        """

        :return:
        """
        # TODO: Remove circular to transaction package to import Transaction classes
        try:
            return self.transaction_stack[-1][0]
        except IndexError:
            return None

    @property
    def instruction(self) -> Dict:
        """

        :return:
        """
        return self.get_current_instruction()

    def new_bitvec(self, name: str, size=256, annotations=None) -> BitVec:
        """

        :param name:
        :param size:
        :return:
        """
        transaction_id = self.current_transaction.id
        return symbol_factory.BitVecSym(
            "{}_{}".format(transaction_id, name), size, annotations=annotations
        )

    def annotate(self, annotation: StateAnnotation) -> None:
        """

        :param annotation:
        """
        self._annotations.append(annotation)

        if annotation.persist_to_world_state:
            self.world_state.annotate(annotation)

    @property
    def annotations(self) -> List[StateAnnotation]:
        """

        :return:
        """
        return self._annotations

    def get_annotations(self, annotation_type: type) -> Iterable[StateAnnotation]:
        """Filters annotations for the queried annotation type. Designed
        particularly for modules with annotations:
        globalstate.get_annotations(MySpecificModuleAnnotation)

        :param annotation_type: The type to filter annotations for
        :return: filter of matching annotations
        """
        return filter(lambda x: isinstance(x, annotation_type), self.annotations)
