"""This module contains the detection code for insecure delegate call usage."""

import logging
from typing import List

from mythril.analysis.swc_data import DOS_WITH_BLOCK_GAS_LIMIT
from mythril.analysis.report import Issue
from mythril.analysis.modules.base import DetectionModule
from mythril.laser.ethereum.state.global_state import GlobalState
from mythril.laser.ethereum.state.annotation import StateAnnotation
from mythril.laser.ethereum import util

log = logging.getLogger(__name__)


class LoopAnnotation(StateAnnotation):
    def __init__(self, jump_address: int) -> None:
        self.jump_address = jump_address


class DOS(DetectionModule):
    """This module detects denial of service by exhausting gas."""

    def __init__(self) -> None:
        """"""
        super().__init__(
            name="DOS",
            swc_id=DOS_WITH_BLOCK_GAS_LIMIT,
            description="Check for DOS",
            entrypoint="callback",
            pre_hooks=["JUMPI", "CALL", "SSTORE"],
        )

        self._jumpdest_count = {}

    def execute(self, state: GlobalState) -> None:
        """

        :param state:
        :return:
        """
        log.debug("Executing module: DOS")

        self._issues.extend(self._analyze_states(state))

    def _analyze_states(self, state: GlobalState) -> List[Issue]:
        """
        :param state: the current state
        :return: returns the issues for that corresponding state
        """

        opcode = state.get_current_instruction()["opcode"]

        if opcode == "JUMPI":

            target = util.get_concrete_int(state.mstate.stack[-1])

            try:
                transaction = state.current_transaction
                self._jumpdest_count[transaction]

                try:
                    if self._jumpdest_count[transaction][target] > 3:
                        state.annotate(
                            LoopAnnotation(state.get_current_instruction()["address"])
                        )
                    else:
                        self._jumpdest_count[transaction][target] += 1
                except KeyError:
                    self._jumpdest_count[transaction][target] = 0

            except KeyError:
                self._jumpdest_count[transaction] = {}
                self._jumpdest_count[transaction][target] = 0

        else:

            for annotation in state.annotations:

                if type(annotation) == LoopAnnotation:

                    operation = (
                        "A storage modification"
                        if opcode == "CALL"
                        else "An external call"
                    )

                    description_head = (
                        "Potential Denial-of-Service if block gas limit is reached."
                    )
                    description_tail = operation + " is executed in a loop."

                    issue = Issue(
                        contract=state.environment.active_account.contract_name,
                        function_name=state.environment.active_function_name,
                        address=annotation.jump_address,
                        swc_id=DOS_WITH_BLOCK_GAS_LIMIT,
                        bytecode=state.environment.code.bytecode,
                        title="Potential Denial-of-Service if block gas limit is reached",
                        severity="Low",
                        description_head=description_head,
                        description_tail=description_tail,
                        gas_used=(state.mstate.min_gas_used, state.mstate.max_gas_used),
                    )
                    return [issue]

        return []


detector = DOS()
