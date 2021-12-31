"""This module contains the detection code for reachable exceptions."""
import logging

from typing import List, cast
from mythril.analysis import solver
from mythril.analysis.module.base import DetectionModule, EntryPoint
from mythril.analysis.report import Issue
from mythril.analysis.swc_data import ASSERT_VIOLATION
from mythril.exceptions import UnsatError
from mythril.laser.ethereum.state.global_state import GlobalState
from mythril.laser.ethereum.state.annotation import StateAnnotation
from mythril.laser.ethereum import util

log = logging.getLogger(__name__)

# The function signature of Panic(uint256)
PANIC_SIGNATURE = [78, 72, 123, 113]


class LastJumpAnnotation(StateAnnotation):
    """State Annotation used if an overflow is both possible and used in the annotated path"""

    def __init__(self, last_jump: int = None) -> None:
        self.last_jump: int = last_jump

    def __copy__(self):
        new_annotation = LastJumpAnnotation(self.last_jump)
        return new_annotation


class Exceptions(DetectionModule):
    """"""

    name = "Assertion violation"
    swc_id = ASSERT_VIOLATION
    description = "Checks whether any exception states are reachable."
    entry_point = EntryPoint.CALLBACK
    pre_hooks = ["INVALID", "JUMP", "REVERT"]

    def _execute(self, state: GlobalState) -> None:
        """

        :param state:
        :return:
        """
        if (
            state.get_current_instruction()["address"],
            state.environment.active_function_name,
        ) in self.cache:
            return
        issues = self._analyze_state(state)
        for issue in issues:
            self.cache.add((issue.address, issue.function))
        self.issues.extend(issues)

    @staticmethod
    def _analyze_state(state) -> List[Issue]:
        """

        :param state:
        :return:
        """
        opcode = state.get_current_instruction()["opcode"]
        address = state.get_current_instruction()["address"]

        annotations = cast(
            List[LastJumpAnnotation],
            [a for a in state.get_annotations(LastJumpAnnotation)],
        )
        if len(annotations) == 0:
            state.annotate(LastJumpAnnotation())
            annotations = cast(
                List[LastJumpAnnotation],
                [a for a in state.get_annotations(LastJumpAnnotation)],
            )

        if opcode == "JUMP":
            annotations[0].last_jump = address
            return []

        if opcode == "REVERT" and not is_assertion_failure(state):
            return []

        log.debug(
            "ASSERT_FAIL/REVERT in function " + state.environment.active_function_name
        )

        try:
            description_tail = (
                "It is possible to trigger an assertion violation. Note that Solidity assert() statements should "
                "only be used to check invariants. Review the transaction trace generated for this issue and "
                "either make sure your program logic is correct, or use require() instead of assert() if your goal "
                "is to constrain user inputs or enforce preconditions. Remember to validate inputs from both callers "
                "(for instance, via passed arguments) and callees (for instance, via return values)."
            )
            transaction_sequence = solver.get_transaction_sequence(
                state, state.world_state.constraints
            )

            issue = Issue(
                contract=state.environment.active_account.contract_name,
                function_name=state.environment.active_function_name,
                address=address,
                swc_id=ASSERT_VIOLATION,
                title="Exception State",
                severity="Medium",
                description_head="An assertion violation was triggered.",
                description_tail=description_tail,
                bytecode=state.environment.code.bytecode,
                transaction_sequence=transaction_sequence,
                gas_used=(state.mstate.min_gas_used, state.mstate.max_gas_used),
                source_location=annotations[0].last_jump,
            )
            return [issue]

        except UnsatError:
            log.debug("no model found")

        return []


def is_assertion_failure(global_state):
    state = global_state.mstate
    offset, length = state.stack[-1], state.stack[-2]
    try:
        return_data = state.memory[
            util.get_concrete_int(offset) : util.get_concrete_int(offset + length)
        ]
    except TypeError:
        return False

    return return_data[:4] == PANIC_SIGNATURE and return_data[-1] == 1


detector = Exceptions()
