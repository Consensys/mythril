"""This module contains the detection code for predictable variable
dependence."""
import logging
from copy import copy

from mythril.analysis.module.base import DetectionModule, EntryPoint
from mythril.analysis.report import Issue
from mythril.exceptions import UnsatError
from mythril.analysis import solver
from mythril.analysis.swc_data import TX_ORIGIN_USAGE
from mythril.laser.ethereum.state.global_state import GlobalState
from typing import List

log = logging.getLogger(__name__)


class TxOriginAnnotation:
    """Symbol annotation added to a variable that is initialized with a call to the ORIGIN instruction."""

    def __init__(self) -> None:
        pass


class TxOrigin(DetectionModule):
    """This module detects whether control flow decisions are made based on the transaction origin."""

    name = "Control flow depends on tx.origin"
    swc_id = TX_ORIGIN_USAGE
    description = "Check whether control flow decisions are influenced by tx.origin"
    entry_point = EntryPoint.CALLBACK

    pre_hooks = ["JUMPI"]
    post_hooks = ["ORIGIN"]

    def _execute(self, state: GlobalState) -> None:
        """

        :param state:
        :return:
        """
        if state.get_current_instruction()["address"] in self.cache:
            return
        issues = self._analyze_state(state)
        for issue in issues:
            self.cache.add(issue.address)
        self.issues.extend(issues)

    @staticmethod
    def _analyze_state(state: GlobalState) -> List[Issue]:
        """

        :param state:
        :return:
        """

        issues = []

        if state.get_current_instruction()["opcode"] == "JUMPI":
            # We're in JUMPI prehook

            for annotation in state.mstate.stack[-2].annotations:

                if isinstance(annotation, TxOriginAnnotation):
                    constraints = copy(state.world_state.constraints)

                    try:
                        transaction_sequence = solver.get_transaction_sequence(
                            state, constraints
                        )
                    except UnsatError:
                        continue

                    description = (
                        "The tx.origin environment variable has been found to influence a control flow decision. "
                        "Note that using tx.origin as a security control might cause a situation where a user "
                        "inadvertently authorizes a smart contract to perform an action on their behalf. It is "
                        "recommended to use msg.sender instead."
                    )

                    severity = "Low"

                    """
                    Note: We report the location of the JUMPI instruction. Usually this maps to an if or
                    require statement.
                    """

                    issue = Issue(
                        contract=state.environment.active_account.contract_name,
                        function_name=state.environment.active_function_name,
                        address=state.get_current_instruction()["address"],
                        swc_id=TX_ORIGIN_USAGE,
                        bytecode=state.environment.code.bytecode,
                        title="Dependence on tx.origin",
                        severity=severity,
                        description_head="Use of tx.origin as a part of authorization control.",
                        description_tail=description,
                        gas_used=(state.mstate.min_gas_used, state.mstate.max_gas_used),
                        transaction_sequence=transaction_sequence,
                    )

                    issues.append(issue)

        else:

            # In ORIGIN posthook

            state.mstate.stack[-1].annotate(TxOriginAnnotation())

        return issues


detector = TxOrigin()
