"""This module contains the detection code for Arbitrary jumps."""
import logging

from mythril.exceptions import UnsatError

from mythril.analysis.solver import get_transaction_sequence, UnsatError
from mythril.analysis.issue_annotation import IssueAnnotation
from mythril.analysis.module.base import DetectionModule, Issue, EntryPoint
from mythril.analysis.swc_data import ARBITRARY_JUMP

from mythril.laser.ethereum.state.global_state import GlobalState
from mythril.laser.smt import And, BitVec, symbol_factory
from mythril.support.model import get_model

log = logging.getLogger(__name__)

DESCRIPTION = """

Search for jumps to arbitrary locations in the bytecode
"""


def is_unique_jumpdest(jump_dest: BitVec, state: GlobalState) -> bool:
    """
    Handles cases where jump_dest evaluates to a single concrete value
    """

    try:
        model = get_model(state.world_state.constraints)
    except UnsatError:
        return True
    concrete_jump_dest = model.eval(jump_dest.raw, model_completion=True)
    try:
        model = get_model(
            state.world_state.constraints
            + [symbol_factory.BitVecVal(concrete_jump_dest.as_long(), 256) != jump_dest]
        )
    except UnsatError:
        return True
    return False


class ArbitraryJump(DetectionModule):
    """This module searches for JUMPs to a user-specified location."""

    name = "Caller can redirect execution to arbitrary bytecode locations"
    swc_id = ARBITRARY_JUMP
    description = DESCRIPTION
    entry_point = EntryPoint.CALLBACK
    pre_hooks = ["JUMP", "JUMPI"]

    def reset_module(self):
        """
        Resets the module by clearing everything
        :return:
        """
        super().reset_module()

    def _execute(self, state: GlobalState) -> None:
        """

        :param state:
        :return:
        """
        return self._analyze_state(state)

    def _analyze_state(self, state):
        """

        :param state:
        :return:
        """

        jump_dest = state.mstate.stack[-1]

        if jump_dest.symbolic is False:
            return []

        if is_unique_jumpdest(jump_dest, state) is True:
            return []

        try:
            transaction_sequence = get_transaction_sequence(
                state, state.world_state.constraints
            )
        except UnsatError:
            return []
        log.info("Detected arbitrary jump dest")
        issue = Issue(
            contract=state.environment.active_account.contract_name,
            function_name=state.environment.active_function_name,
            address=state.get_current_instruction()["address"],
            swc_id=ARBITRARY_JUMP,
            title="Jump to an arbitrary instruction",
            severity="High",
            bytecode=state.environment.code.bytecode,
            description_head="The caller can redirect execution to arbitrary bytecode locations.",
            description_tail="It is possible to redirect the control flow to arbitrary locations in the code. "
            "This may allow an attacker to bypass security controls or manipulate the business logic of the "
            "smart contract. Avoid using low-level-operations and assembly to prevent this issue.",
            gas_used=(state.mstate.min_gas_used, state.mstate.max_gas_used),
            transaction_sequence=transaction_sequence,
        )
        state.annotate(
            IssueAnnotation(
                conditions=[And(*state.world_state.constraints)],
                issue=issue,
                detector=self,
            )
        )

        return [issue]


detector = ArbitraryJump()
