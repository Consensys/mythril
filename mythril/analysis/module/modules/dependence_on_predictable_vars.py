"""This module contains the detection code for predictable variable
dependence."""
import logging

from mythril.analysis.module.base import DetectionModule, EntryPoint
from mythril.analysis.report import Issue
from mythril.exceptions import UnsatError
from mythril.analysis import solver
from mythril.laser.smt import ULT, symbol_factory
from mythril.analysis.swc_data import TIMESTAMP_DEPENDENCE, WEAK_RANDOMNESS
from mythril.analysis.module.module_helpers import is_prehook
from mythril.laser.ethereum.state.global_state import GlobalState
from mythril.laser.ethereum.state.annotation import StateAnnotation
from typing import cast, List

log = logging.getLogger(__name__)

predictable_ops = ["COINBASE", "GASLIMIT", "TIMESTAMP", "NUMBER"]


class PredictableValueAnnotation:
    """Symbol annotation used if a variable is initialized from a predictable environment variable."""

    def __init__(self, operation: str) -> None:
        self.operation = operation


class OldBlockNumberUsedAnnotation(StateAnnotation):
    """Symbol annotation used if a variable is initialized from a predictable environment variable."""

    def __init__(self) -> None:
        pass


class PredictableVariables(DetectionModule):
    """This module detects whether control flow decisions are made using predictable
    parameters."""

    name = "Control flow depends on a predictable environment variable"
    swc_id = "{} {}".format(TIMESTAMP_DEPENDENCE, WEAK_RANDOMNESS)
    description = (
        "Check whether control flow decisions are influenced by block.coinbase,"
        "block.gaslimit, block.timestamp or block.number."
    )
    entry_point = EntryPoint.CALLBACK
    pre_hooks = ["JUMPI", "BLOCKHASH"]
    post_hooks = ["BLOCKHASH"] + predictable_ops

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

        if is_prehook():

            opcode = state.get_current_instruction()["opcode"]

            if opcode == "JUMPI":

                # Look for predictable state variables in jump condition

                for annotation in state.mstate.stack[-2].annotations:

                    if isinstance(annotation, PredictableValueAnnotation):

                        constraints = state.world_state.constraints
                        try:
                            transaction_sequence = solver.get_transaction_sequence(
                                state, constraints
                            )
                        except UnsatError:
                            continue
                        description = (
                            annotation.operation
                            + " is used to determine a control flow decision. "
                        )
                        description += (
                            "Note that the values of variables like coinbase, gaslimit, block number and timestamp are "
                            "predictable and can be manipulated by a malicious miner. Also keep in mind that "
                            "attackers know hashes of earlier blocks. Don't use any of those environment variables "
                            "as sources of randomness and be aware that use of these variables introduces "
                            "a certain level of trust into miners."
                        )

                        """
                        Usually report low severity except in cases where the hash of a previous block is used to
                        determine control flow. 
                        """

                        severity = "Low"

                        swc_id = (
                            TIMESTAMP_DEPENDENCE
                            if "timestamp" in annotation.operation
                            else WEAK_RANDOMNESS
                        )

                        issue = Issue(
                            contract=state.environment.active_account.contract_name,
                            function_name=state.environment.active_function_name,
                            address=state.get_current_instruction()["address"],
                            swc_id=swc_id,
                            bytecode=state.environment.code.bytecode,
                            title="Dependence on predictable environment variable",
                            severity=severity,
                            description_head="A control flow decision is made based on {}.".format(
                                annotation.operation
                            ),
                            description_tail=description,
                            gas_used=(
                                state.mstate.min_gas_used,
                                state.mstate.max_gas_used,
                            ),
                            transaction_sequence=transaction_sequence,
                        )

                        issues.append(issue)

            elif opcode == "BLOCKHASH":

                param = state.mstate.stack[-1]

                constraint = [
                    ULT(param, state.environment.block_number),
                    ULT(
                        state.environment.block_number,
                        symbol_factory.BitVecVal(2 ** 255, 256),
                    ),
                ]

                # Why the second constraint? Because without it Z3 returns a solution where param overflows.

                try:

                    solver.get_model(
                        state.world_state.constraints + constraint  # type: ignore
                    )

                    state.annotate(OldBlockNumberUsedAnnotation())

                except UnsatError:
                    pass

        else:
            # we're in post hook

            opcode = state.environment.code.instruction_list[state.mstate.pc - 1][
                "opcode"
            ]

            if opcode == "BLOCKHASH":
                # if we're in the post hook of a BLOCKHASH op, check if an old block number was used to create it.

                annotations = cast(
                    List[OldBlockNumberUsedAnnotation],
                    list(state.get_annotations(OldBlockNumberUsedAnnotation)),
                )

                if len(annotations):
                    # We can append any block constraint here
                    state.mstate.stack[-1].annotate(
                        PredictableValueAnnotation("The block hash of a previous block")
                    )
            else:
                # Always create an annotation when COINBASE, GASLIMIT, TIMESTAMP or NUMBER is executed.

                state.mstate.stack[-1].annotate(
                    PredictableValueAnnotation(
                        "The block.{} environment variable".format(opcode.lower())
                    )
                )

        return issues


detector = PredictableVariables()
