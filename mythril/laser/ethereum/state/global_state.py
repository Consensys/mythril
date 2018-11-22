from typing import Dict, Union

from copy import copy, deepcopy
from z3 import BitVec

from mythril.laser.ethereum.cfg import Node
from mythril.laser.ethereum.state.environment import Environment
from mythril.laser.ethereum.state.machine_state import MachineState


class GlobalState:
    """
    GlobalState represents the current globalstate
    """

    def __init__(
        self,
        world_state: "WorldState",
        environment: Environment,
        node: Node,
        machine_state=None,
        transaction_stack=None,
        last_return_data=None,
        annotations=None
    ):
        """ Constructor for GlobalState"""
        self.node = node
        self.world_state = world_state
        self.environment = environment
        self.mstate = (
            machine_state if machine_state else MachineState(gas_limit=1000000000)
        )
        self.transaction_stack = transaction_stack if transaction_stack else []
        self.op_code = ""
        self.last_return_data = last_return_data
        self.annotations = annotations or []

    def __copy__(self) -> "GlobalState":
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
            annotations=self.annotations
        )

    @property
    def accounts(self) -> Dict:
        return self.world_state.accounts

    # TODO: remove this, as two instructions are confusing
    def get_current_instruction(self) -> Dict:
        """ Gets the current instruction for this GlobalState"""

        instructions = self.environment.code.instruction_list
        return instructions[self.mstate.pc]

    @property
    def current_transaction(
        self
    ) -> Union["MessageCallTransaction", "ContractCreationTransaction", None]:
        # TODO: Remove circular to transaction package to import Transaction classes
        try:
            return self.transaction_stack[-1][0]
        except IndexError:
            return None

    @property
    def instruction(self) -> Dict:
        return self.get_current_instruction()

    def new_bitvec(self, name: str, size=256) -> BitVec:
        transaction_id = self.current_transaction.id
        return BitVec("{}_{}".format(transaction_id, name), size)
