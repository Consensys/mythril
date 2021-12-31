"""This module contains the detection code for potentially insecure low-level
calls."""

from mythril.analysis import solver
from mythril.analysis.potential_issues import Issue
from mythril.analysis.swc_data import ASSERT_VIOLATION
from mythril.analysis.module.base import DetectionModule, EntryPoint
from mythril.laser.ethereum.state.global_state import GlobalState
from mythril.laser.smt import Extract
from mythril.exceptions import UnsatError
import logging
import eth_abi

log = logging.getLogger(__name__)

DESCRIPTION = """

Search for reachable user-supplied exceptions.
Report a warning if an log message is emitted: 'emit AssertionFailed(string)'

"""

assertion_failed_hash = (
    0xB42604CB105A16C8F6DB8A41E6B00C0C1B4826465E8BC504B3EB3E88B3E6A4A0
)

mstore_pattern = "0xcafecafecafecafecafecafecafecafecafecafecafecafecafecafecafe"


class UserAssertions(DetectionModule):
    """This module searches for user supplied exceptions: emit AssertionFailed("Error")."""

    name = "A user-defined assertion has been triggered"
    swc_id = ASSERT_VIOLATION
    description = DESCRIPTION
    entry_point = EntryPoint.CALLBACK
    pre_hooks = ["LOG1", "MSTORE"]

    def _execute(self, state: GlobalState) -> None:
        """

        :param state:
        :return:
        """

        issues = self._analyze_state(state)
        for issue in issues:
            self.cache.add(issue.address)
        self.issues.extend(issues)

    def _analyze_state(self, state: GlobalState):
        """

        :param state:
        :return:
        """
        opcode = state.get_current_instruction()["opcode"]
        message = None
        if opcode == "MSTORE":
            value = state.mstate.stack[-2]
            if value.symbolic:
                return []
            if mstore_pattern not in hex(value.value)[:126]:
                return []
            message = "Failed property id {}".format(Extract(15, 0, value).value)

        else:
            topic, size, mem_start = state.mstate.stack[-3:]

            if topic.symbolic or topic.value != assertion_failed_hash:
                return []
            if not mem_start.symbolic and not size.symbolic:
                try:
                    message = eth_abi.decode_single(
                        "string",
                        bytes(
                            state.mstate.memory[
                                mem_start.value + 32 : mem_start.value + size.value
                            ]
                        ),
                    ).decode("utf8")
                except:
                    pass
        try:
            transaction_sequence = solver.get_transaction_sequence(
                state, state.world_state.constraints
            )

            if message:
                description_tail = (
                    "A user-provided assertion failed with the message '{}'".format(
                        message
                    )
                )

            else:
                description_tail = "A user-provided assertion failed."

            log.debug("MythX assertion emitted: {}".format(description_tail))

            address = state.get_current_instruction()["address"]

            issue = Issue(
                contract=state.environment.active_account.contract_name,
                function_name=state.environment.active_function_name,
                address=address,
                swc_id=ASSERT_VIOLATION,
                title="Exception State",
                severity="Medium",
                description_head="A user-provided assertion failed.",
                description_tail=description_tail,
                bytecode=state.environment.code.bytecode,
                transaction_sequence=transaction_sequence,
                gas_used=(state.mstate.min_gas_used, state.mstate.max_gas_used),
            )
            return [issue]

        except UnsatError:
            log.debug("no model found")

        return []


detector = UserAssertions()
