"""This module contains the detection code SWC-128 - DOS with block gas limit."""

import logging
from typing import Dict, cast, List

from mythril.analysis.swc_data import DOS_WITH_BLOCK_GAS_LIMIT
from mythril.analysis.report import Issue
from mythril.analysis.modules.base import DetectionModule
from mythril.laser.ethereum.state.global_state import GlobalState
from mythril.laser.ethereum.state.annotation import StateAnnotation
from copy import copy

log = logging.getLogger(__name__)


class VisitsAnnotation(StateAnnotation):
    """State annotation that stores the addresses of state-modifying operations"""

    def __init__(self) -> None:
        self.last_jumpdest = 0
        self._visited = {}  # type: Dict[int, str]

    def __copy__(self):
        result = VisitsAnnotation()
        result.last_jumpdest = self.last_jumpdest
        result._visited = copy(self._visited)
        return result


class DOS(DetectionModule):
    """This module consists of a makeshift loop detector that annotates the state with
    a list of byte ranges likely to be loops. If a CALL or SSTORE detection is found in
    one of the ranges it creates a low-severity issue. This is not super precise but
    good enough to identify places that warrant a closer look. Checking the loop condition
    would be a possible improvement.
     """

    def __init__(self) -> None:
        """"""
        super().__init__(
            name="DOS",
            swc_id=DOS_WITH_BLOCK_GAS_LIMIT,
            description="Check for DOS",
            entrypoint="callback",
            pre_hooks=["JUMPDEST", "CALL", "SSTORE"],
        )

    def _execute(self, state: GlobalState) -> None:

        """
        :param state:
        :return:
        """

        self._issues.extend(self._analyze_states(state))

    def _analyze_states(self, state: GlobalState) -> List[Issue]:
        """
        :param state: the current state
        :return: returns the issues for that corresponding state
        """

        opcode = state.get_current_instruction()["opcode"]
        address = state.get_current_instruction()["address"]

        annotations = cast(
            List[VisitsAnnotation], list(state.get_annotations(VisitsAnnotation))
        )

        if len(annotations) == 0:
            annotation = VisitsAnnotation()
            state.annotate(annotation)
        else:
            annotation = annotations[0]

        if opcode == "JUMPDEST":
            annotation.last_jumpdest == address

        if address in annotation._visited:

            if annotation._visited[address] == "CALL":
                operation = "A message call"
            else:
                operation = "A storage modification"

            description_head = (
                "Potential denial-of-service if block gas limit is reached."
            )
            description_tail = "{} is executed in a loop. Be aware that the transaction may fail to execute if the loop is unbounded and the necessary gas exceeds the block gas limit. ".format(
                operation
            )

            issue = Issue(
                contract=state.environment.active_account.contract_name,
                function_name=state.environment.active_function_name,
                address=annotation.last_jumpdest,
                swc_id=DOS_WITH_BLOCK_GAS_LIMIT,
                bytecode=state.environment.code.bytecode,
                title="Potential denial-of-service if block gas limit is reached",
                severity="Low",
                description_head=description_head,
                description_tail=description_tail,
                gas_used=(state.mstate.min_gas_used, state.mstate.max_gas_used),
            )

            return [issue]

        else:
            annotation._visited[address] = opcode

        return []


detector = DOS()
