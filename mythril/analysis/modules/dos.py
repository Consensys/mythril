"""This module contains the detection code SWC-128 - DOS with block gas limit."""

import logging
from typing import Dict, cast, List

from mythril.analysis.swc_data import DOS_WITH_BLOCK_GAS_LIMIT
from mythril.analysis.report import Issue
from mythril.analysis.modules.base import DetectionModule
from mythril.laser.ethereum.state.global_state import GlobalState
from mythril.laser.ethereum.state.annotation import StateAnnotation
from mythril.laser.ethereum import util

log = logging.getLogger(__name__)


class LoopAnnotation(StateAnnotation):
    def __init__(self, loop_start: int, loop_end: int) -> None:
        self.loop_start = loop_start
        self.loop_end = loop_end

    def contains(self, address: int) -> bool:
        return self.loop_start < address < self.loop_end


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
            pre_hooks=["JUMPI", "CALL", "SSTORE"],
        )

        """Keeps track of how often jump destinations are reached."""
        self._jumpdest_count = {}  # type: Dict[object, dict]

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

        if opcode == "JUMPI":

            target = util.get_concrete_int(state.mstate.stack[-1])

            transaction = state.current_transaction
            if state.current_transaction in self._jumpdest_count:

                try:
                    self._jumpdest_count[transaction][target] += 1
                    if self._jumpdest_count[transaction][target] == 4:

                        annotation = (
                            LoopAnnotation(address, target)
                            if target > address
                            else LoopAnnotation(target, address)
                        )

                        state.annotate(annotation)
                except KeyError:
                    self._jumpdest_count[transaction][target] = 0

            else:
                self._jumpdest_count[transaction] = {}
                self._jumpdest_count[transaction][target] = 0

        else:

            annotations = cast(
                List[LoopAnnotation], list(state.get_annotations(LoopAnnotation))
            )

            for annotation in annotations:

                if annotation.contains(address):

                    operation = (
                        "A storage modification"
                        if opcode == "SSTORE"
                        else "An external call"
                    )

                    description_head = (
                        "Potential denial-of-service if block gas limit is reached."
                    )
                    description_tail = "{} is executed in a loop.".format(operation)

                    issue = Issue(
                        contract=state.environment.active_account.contract_name,
                        function_name=state.environment.active_function_name,
                        address=annotation.loop_start,
                        swc_id=DOS_WITH_BLOCK_GAS_LIMIT,
                        bytecode=state.environment.code.bytecode,
                        title="Potential denial-of-service if block gas limit is reached",
                        severity="Low",
                        description_head=description_head,
                        description_tail=description_tail,
                        gas_used=(state.mstate.min_gas_used, state.mstate.max_gas_used),
                    )
                    return [issue]

        return []


detector = DOS()
