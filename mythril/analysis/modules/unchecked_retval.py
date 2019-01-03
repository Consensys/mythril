"""This module contains detection code to find occurrences of calls whose
return value remains unchecked."""
from copy import copy

from mythril.analysis import solver
from mythril.analysis.report import Issue
from mythril.analysis.swc_data import UNCHECKED_RET_VAL
from mythril.analysis.modules.base import DetectionModule
from mythril.exceptions import UnsatError
from mythril.laser.ethereum.state.annotation import StateAnnotation
from mythril.laser.ethereum.state.global_state import GlobalState

import logging

log = logging.getLogger(__name__)


class UncheckedRetvalAnnotation(StateAnnotation):
    def __init__(self):
        self.retvals = []

    def __copy__(self):
        result = UncheckedRetvalAnnotation()
        result.retvals = copy(self.retvals)
        return result


class UncheckedRetvalModule(DetectionModule):
    """A detection module to test whether CALL return value is checked."""

    def __init__(self):
        super().__init__(
            name="Unchecked Return Value",
            swc_id=UNCHECKED_RET_VAL,
            description=(
                "Test whether CALL return value is checked. "
                "For direct calls, the Solidity compiler auto-generates this check. E.g.:\n"
                "    Alice c = Alice(address);\n"
                "    c.ping(42);\n"
                "Here the CALL will be followed by IZSERO(retval), if retval = ZERO then state is reverted. "
                "For low-level-calls this check is omitted. E.g.:\n"
                '    c.call.value(0)(bytes4(sha3("ping(uint256)")),1);'
            ),
            entrypoint="callback",
            pre_hooks=["STOP", "RETURN"],
            post_hooks=["CALL", "DELEGATECALL", "STATICCALL", "CALLCODE"],
        )

    def execute(self, state: GlobalState) -> list:
        """

        :param state:
        :return:
        """
        self._issues.extend(_analyze_state(state))
        return self.issues


def _analyze_state(state: GlobalState) -> list:
    instruction = state.get_current_instruction()
    node = state.node

    annotations = [a for a in state.get_annotations(UncheckedRetvalAnnotation)]
    if len(annotations) == 0:
        state.annotate(UncheckedRetvalAnnotation())
        annotations = [a for a in state.get_annotations(UncheckedRetvalAnnotation)]

    retvals = annotations[0].retvals

    if instruction["opcode"] in ("STOP", "RETURN"):
        issues = []
        for retval in retvals:
            try:
                model = solver.get_model(node.constraints + [retval["retval"] == 0])
            except UnsatError:
                continue

            issue = Issue(
                contract=node.contract_name,
                function_name=node.function_name,
                address=retval["address"],
                bytecode=state.environment.code.bytecode,
                title="Unchecked CALL return value",
                swc_id=UNCHECKED_RET_VAL,
                gas_used=(state.mstate.min_gas_used, state.mstate.max_gas_used),
            )

            issue.description = (
                "The return value of an external call is not checked. "
                "Note that execution continue even if the called contract throws."
            )
            issues.append(issue)

        return issues
    else:
        log.debug("End of call, extracting retval")
        assert state.environment.code.instruction_list[state.mstate.pc - 1][
            "opcode"
        ] in ["CALL", "DELEGATECALL", "STATICCALL", "CALLCODE"]
        retval = state.mstate.stack[-1]
        retvals.append({"address": state.instruction["address"] - 1, "retval": retval})

    return []


detector = UncheckedRetvalModule()
