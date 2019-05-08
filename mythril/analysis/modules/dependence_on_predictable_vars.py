"""This module contains the detection code for predictable variable
dependence."""
import logging

from mythril.analysis.modules.base import DetectionModule
from mythril.analysis.report import Issue
from mythril.analysis.swc_data import TIMESTAMP_DEPENDENCE, WEAK_RANDOMNESS
from mythril.laser.ethereum.state.global_state import GlobalState

log = logging.getLogger(__name__)


class PredictableDependenceModule(DetectionModule):
    """This module detects whether control flow decisions are made using predictable
    parameters."""

    def __init__(self) -> None:
        """"""
        super().__init__(
            name="Dependence of Predictable Variables",
            swc_id="{} {}".format(TIMESTAMP_DEPENDENCE, WEAK_RANDOMNESS),
            description=(
                "Check whether control flow decisions are influenced by block.coinbase,"
                "block.gaslimit, block.timestamp or block.number."
            ),
            entrypoint="callback",
            pre_hooks=["JUMPI"],
        )

    def execute(self, state: GlobalState) -> list:
        """

        :param state:
        :return:
        """
        log.debug("Executing module: DEPENDENCE_ON_PREDICTABLE_VARS")
        self._issues.extend(_analyze_states(state))
        return self.issues


detector = PredictableDependenceModule()


def _analyze_states(state: GlobalState) -> list:
    """

    :param state:
    :return:
    """
    issues = []

    # Look for predictable state variables in jump condition

    vars = ["coinbase", "gaslimit", "timestamp", "number"]
    found = []

    description = "A control flow decision is made based on "

    for var in vars:
        if var in str(state.mstate.stack[-2]):
            found.append(var)

    if len(found):
        for item in found:
            description += "block.{}. ".format(item)
            swc_id = TIMESTAMP_DEPENDENCE if item == "timestamp" else WEAK_RANDOMNESS

            description += (
                "Note that the values of variables like coinbase, gaslimit, block number and timestamp "
                "are predictable and can be manipulated by a malicious miner. "
                "Don't use them for random number generation or to make critical control flow decisions."
            )

            issue = Issue(
                contract=state.environment.active_account.contract_name,
                function_name=state.environment.active_function_name,
                address=state.get_current_instruction()["address"],
                swc_id=swc_id,
                bytecode=state.environment.code.bytecode,
                title="Dependence on predictable environment variable",
                severity="Low",
                description_head="A control flow decision is made based on a predictable variable.",
                description_tail=description,
                gas_used=(state.mstate.min_gas_used, state.mstate.max_gas_used),
            )
            issues.append(issue)

    return issues
