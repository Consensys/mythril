"""This module."""
from enum import Enum
from typing import Dict, List, TYPE_CHECKING

from flags import Flags

if TYPE_CHECKING:
    from mythril.laser.ethereum.state.global_state import GlobalState

gbl_next_uid = 0  # node counter


class JumpType(Enum):
    """An enum to represent the types of possible JUMP scenarios."""

    CONDITIONAL = 1
    UNCONDITIONAL = 2
    CALL = 3
    RETURN = 4
    Transaction = 5


class NodeFlags(Flags):
    """A collection of flags to denote the type a call graph node can have."""

    FUNC_ENTRY = 1
    CALL_RETURN = 2


class Node:
    """The representation of a call graph node."""

    def __init__(
        self,
        contract_name: str,
        start_addr=0,
        constraints=None,
        function_name="unknown",
    ) -> None:
        """

        :param contract_name:
        :param start_addr:
        :param constraints:
        """
        constraints = constraints if constraints else []
        self.contract_name = contract_name
        self.start_addr = start_addr
        self.states = []  # type: List[GlobalState]
        self.constraints = constraints
        self.function_name = function_name
        self.flags = NodeFlags()

        # Self-assign a unique ID
        global gbl_next_uid

        self.uid = gbl_next_uid
        gbl_next_uid += 1

    def get_cfg_dict(self) -> Dict:
        """

        :return:
        """
        code = ""
        for state in self.states:
            instruction = state.get_current_instruction()

            code += str(instruction["address"]) + " " + instruction["opcode"]
            if instruction["opcode"].startswith("PUSH"):
                code += " " + instruction["argument"]

            code += "\\n"

        return dict(
            contract_name=self.contract_name,
            start_addr=self.start_addr,
            function_name=self.function_name,
            code=code,
        )


class Edge:
    """The respresentation of a call graph edge."""

    def __init__(
        self,
        node_from: int,
        node_to: int,
        edge_type=JumpType.UNCONDITIONAL,
        condition=None,
    ) -> None:
        """

        :param node_from:
        :param node_to:
        :param edge_type:
        :param condition:
        """
        self.node_from = node_from
        self.node_to = node_to
        self.type = edge_type
        self.condition = condition

    def __str__(self) -> str:
        """

        :return:
        """
        return str(self.as_dict)

    @property
    def as_dict(self) -> Dict[str, int]:
        """

        :return:
        """
        return {"from": self.node_from, "to": self.node_to}
