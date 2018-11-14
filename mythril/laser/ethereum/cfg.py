from flags import Flags
from enum import Enum
from typing import Dict

gbl_next_uid = 0  # node counter


class JumpType(Enum):
    CONDITIONAL = 1
    UNCONDITIONAL = 2
    CALL = 3
    RETURN = 4
    Transaction = 5


class NodeFlags(Flags):
    FUNC_ENTRY = 1
    CALL_RETURN = 2


class Node:
    def __init__(self, contract_name: str, start_addr=0, constraints=None):
        constraints = constraints if constraints else []
        self.contract_name = contract_name
        self.start_addr = start_addr
        self.states = []
        self.constraints = constraints
        self.function_name = "unknown"
        self.flags = NodeFlags()

        # Self-assign a unique ID
        global gbl_next_uid

        self.uid = gbl_next_uid
        gbl_next_uid += 1

    def get_cfg_dict(self) -> Dict:
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
    def __init__(
        self,
        node_from: int,
        node_to: int,
        edge_type=JumpType.UNCONDITIONAL,
        condition=None,
    ):
        self.node_from = node_from
        self.node_to = node_to
        self.type = edge_type
        self.condition = condition

    def __str__(self) -> str:
        return str(self.as_dict)

    @property
    def as_dict(self) -> Dict[str, int]:
        return {"from": self.node_from, "to": self.node_to}
