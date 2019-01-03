"""This module contains the detection code for reachable exceptions."""
import logging

from mythril.analysis import solver
from mythril.analysis.modules.base import DetectionModule
from mythril.analysis.report import Issue
from mythril.analysis.swc_data import ASSERT_VIOLATION
from mythril.exceptions import UnsatError
from mythril.laser.ethereum.state.global_state import GlobalState

log = logging.getLogger(__name__)


def _analyze_state(state) -> list:
    """

    :param state:
    :return:
    """
    log.info("Exceptions module: found ASSERT_FAIL instruction")
    node = state.node

    log.debug("ASSERT_FAIL in function " + node.function_name)

    try:
        address = state.get_current_instruction()["address"]

        description = (
            "A reachable exception (opcode 0xfe) has been detected. "
            "This can be caused by type errors, division by zero, "
            "out-of-bounds array access, or assert violations. "
            "Note that explicit `assert()` should only be used to check invariants. "
            "Use `require()` for regular input checking."
        )

        debug = str(solver.get_transaction_sequence(state, node.constraints))

        issue = Issue(
            contract=node.contract_name,
            function_name=node.function_name,
            address=address,
            swc_id=ASSERT_VIOLATION,
            title="Exception state",
            _type="Informational",
            description=description,
            bytecode=state.environment.code.bytecode,
            debug=debug,
            gas_used=(state.mstate.min_gas_used, state.mstate.max_gas_used),
        )
        return [issue]

    except UnsatError:
        log.debug("no model found")

    return []


class ReachableExceptionsModule(DetectionModule):
    """"""

    def __init__(self):
        """"""
        super().__init__(
            name="Reachable Exceptions",
            swc_id=ASSERT_VIOLATION,
            description="Checks whether any exception states are reachable.",
            entrypoint="callback",
            pre_hooks=["ASSERT_FAIL"],
        )
        self._issues = []

    def execute(self, state: GlobalState) -> list:
        """

        :param state:
        :return:
        """
        self._issues.extend(_analyze_state(state))
        return self.issues

    @property
    def issues(self) -> list:
        """

        :return:
        """
        return self._issues


detector = ReachableExceptionsModule()
