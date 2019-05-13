"""This module contains the detection code for predictable variable
dependence."""
import logging

from mythril.analysis.modules.base import DetectionModule
from mythril.analysis.report import Issue
from mythril.exceptions import UnsatError
from mythril.analysis import solver
from mythril.laser.smt import ULT
from mythril.analysis.swc_data import TIMESTAMP_DEPENDENCE, WEAK_RANDOMNESS
from mythril.laser.ethereum.state.global_state import GlobalState
from mythril.laser.ethereum.state.annotation import StateAnnotation
import traceback

log = logging.getLogger(__name__)

predictable_ops = ["COINBASE", "GASLIMIT", "TIMESTAMP", "NUMBER"]


def is_prehook():
    return "pre_hook" in traceback.format_stack()[-2]


class PredictableValueAnnotation:
    """ Symbol Annotation used if a variable is initialized from a predictable environment variable"""

    def __init__(self, opcode) -> None:
        self.opcode = opcode


class TaintBlockHashAnnotation(StateAnnotation):

    def __init__(self) -> None:
        pass


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
            pre_hooks=["BLOCKHASH", "JUMPI"],
            post_hooks=["BLOCKHASH"] + predictable_ops,
        )

    def execute(self, state: GlobalState) -> list:
        """

        :param state:
        :return:
        """

        log.info("Executing module: DEPENDENCE_ON_PREDICTABLE_VARS")

        self._issues.extend(_analyze_states(state))
        return self.issues


def _analyze_states(state: GlobalState) -> list:
    """

    :param state:
    :return:
    """
    issues = []

    # Look for predictable state variables in jump condition

    if state.get_current_instruction()["opcode"] == "JUMPI":
        for annotation in state.mstate.stack[-2].annotations:
            if isinstance(annotation, PredictableValueAnnotation):
                description = "A control flow decision is made based on block.{}. ".format(
                    annotation.opcode
                )

                description += (
                    "Note that the values of variables like coinbase, gaslimit, block number and timestamp "
                    "are predictable and can be manipulated by a malicious miner. "
                    "Don't use them for random number generation or to make critical control flow decisions."
                )

                issue = Issue(
                    contract=state.environment.active_account.contract_name,
                    function_name=state.environment.active_function_name,
                    address=state.get_current_instruction()["address"],
                    swc_id=TIMESTAMP_DEPENDENCE,
                    bytecode=state.environment.code.bytecode,
                    title="Dependence on predictable environment variable",
                    severity="Low",
                    description_head="A control flow decision is made based on a predictable variable.",
                    description_tail=description,
                    gas_used=(state.mstate.min_gas_used, state.mstate.max_gas_used),
                )
                issues.append(issue)
    elif state.get_current_instruction()["opcode"] == "BLOCKHASH":
        if is_prehook():

            param = state.mstate.stack[-1]

            try:
                solver.get_model(ULT(param, state.environment.block_number))
                state.annotate(TaintBlockHashAnnotation)

            except UnsatError:
                pass
        else:
            for annotation in state.annotations:
                if isinstance(annotation, TaintBlockHashAnnotation):
                    state.mstate.stack[-1].annotate(PredictableValueAnnotation("BLOCKHASH"))
    else:
        # we're in post hook

        instructions = state.environment.code.instruction_list
        opcode = instructions[state.mstate.pc - 1]["opcode"]

        annotation = PredictableValueAnnotation(opcode)
        state.mstate.stack[-1].annotate(annotation)

    return issues


detector = PredictableDependenceModule()
