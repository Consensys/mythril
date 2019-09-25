"""This module contains the detection code for predictable variable
dependence."""
import logging
from copy import copy

from mythril.analysis.modules.base import DetectionModule
from mythril.analysis.report import Issue
from mythril.exceptions import UnsatError
from mythril.analysis import solver
from mythril.laser.smt import ULT, symbol_factory
from mythril.analysis.swc_data import TIMESTAMP_DEPENDENCE, WEAK_RANDOMNESS
from mythril.laser.ethereum.state.global_state import GlobalState
from mythril.laser.ethereum.state.annotation import StateAnnotation
from typing import cast, List
import traceback

log = logging.getLogger(__name__)

predictable_ops = ["COINBASE", "GASLIMIT", "TIMESTAMP", "NUMBER"]
final_ops = ["CALL", "SUICIDE", "STOP", "RETURN"]


def is_prehook() -> bool:
    """Check if we are in prehook.  One of Bernhard's trademark hacks!"""
    return "pre_hook" in traceback.format_stack()[-5]


class PredictableValueAnnotation:
    """Symbol annotation used if a variable is initialized from a predictable environment variable."""

    def __init__(self, operation: str, add_constraints=None) -> None:
        self.operation = operation
        self.add_constraints = add_constraints


class PredictablePathAnnotation(StateAnnotation):
    """State annotation used when a path is chosen based on a predictable variable."""

    def __init__(self, operation: str, location: int, add_constraints=None) -> None:
        self.operation = operation
        self.location = location
        self.add_constraints = add_constraints


class OldBlockNumberUsedAnnotation(StateAnnotation):
    """State annotation set in blockhash prehook if the input value is lower than the current block number."""

    def __init__(self, constraints) -> None:
        self.block_constraints = constraints
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
                "Check whether important control flow decisions are influenced by block.coinbase,"
                "block.gaslimit, block.timestamp or block.number."
            ),
            entrypoint="callback",
            pre_hooks=["BLOCKHASH", "JUMPI"] + final_ops,
            post_hooks=["BLOCKHASH"] + predictable_ops,
        )

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
    def _analyze_state(state: GlobalState) -> list:
        """

        :param state:
        :return:
        """

        issues = []

        if is_prehook():

            opcode = state.get_current_instruction()["opcode"]

            if opcode in final_ops:

                for annotation in state.annotations:

                    if isinstance(annotation, PredictablePathAnnotation):
                        if annotation.add_constraints:
                            constraints = (
                                state.mstate.constraints + annotation.add_constraints
                            )
                        else:
                            constraints = copy(state.mstate.constraints)
                        try:
                            transaction_sequence = solver.get_transaction_sequence(
                                state, constraints
                            )
                        except UnsatError:
                            continue
                        description = (
                            "The "
                            + annotation.operation
                            + " is used in to determine a control flow decision. "
                        )
                        description += (
                            "Note that the values of variables like coinbase, gaslimit, block number and timestamp "
                            "are predictable and can be manipulated by a malicious miner. Also keep in mind that attackers "
                            "know hashes of earlier blocks. Don't use any of those environment variables for random number "
                            "generation or to make critical control flow decisions."
                        )

                        """
                        Usually report low severity except in cases where the hash of a previous block is used to
                        determine control flow. 
                        """

                        severity = "Medium" if "hash" in annotation.operation else "Low"

                        """
                        Note: We report the location of the JUMPI that lead to this path. Usually this maps to an if or
                        require statement.
                        """

                        swc_id = (
                            TIMESTAMP_DEPENDENCE
                            if "timestamp" in annotation.operation
                            else WEAK_RANDOMNESS
                        )

                        issue = Issue(
                            contract=state.environment.active_account.contract_name,
                            function_name=state.environment.active_function_name,
                            address=annotation.location,
                            swc_id=swc_id,
                            bytecode=state.environment.code.bytecode,
                            title="Dependence on predictable environment variable",
                            severity=severity,
                            description_head="A control flow decision is made based on a predictable variable.",
                            description_tail=description,
                            gas_used=(
                                state.mstate.min_gas_used,
                                state.mstate.max_gas_used,
                            ),
                            transaction_sequence=transaction_sequence,
                        )

                        issues.append(issue)

            elif opcode == "JUMPI":

                # Look for predictable state variables in jump condition

                for annotation in state.mstate.stack[-2].annotations:

                    if isinstance(annotation, PredictableValueAnnotation):
                        state.annotate(
                            PredictablePathAnnotation(
                                annotation.operation,
                                state.get_current_instruction()["address"],
                                add_constraints=annotation.add_constraints,
                            )
                        )
                        break

            elif opcode == "BLOCKHASH":

                param = state.mstate.stack[-1]

                try:
                    constraint = [
                        ULT(param, state.environment.block_number),
                        ULT(
                            state.environment.block_number,
                            symbol_factory.BitVecVal(2 ** 255, 256),
                        ),
                    ]

                    # Why the second constraint? Because without it Z3 returns a solution where param overflows.

                    solver.get_model(state.mstate.constraints + constraint)
                    state.annotate(OldBlockNumberUsedAnnotation(constraint))

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
                        PredictableValueAnnotation(
                            "block hash of a previous block",
                            add_constraints=annotations[0].block_constraints,
                        )
                    )
            else:
                # Always create an annotation when COINBASE, GASLIMIT, TIMESTAMP or NUMBER is executed.

                state.mstate.stack[-1].annotate(
                    PredictableValueAnnotation(
                        "block.{} environment variable".format(opcode.lower())
                    )
                )

        return issues


detector = PredictableDependenceModule()
