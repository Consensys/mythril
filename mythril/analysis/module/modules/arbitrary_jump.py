"""This module contains the detection code for Arbitrary jumps."""
import logging
from mythril.analysis.solver import get_transaction_sequence, UnsatError
from mythril.analysis.module.base import DetectionModule, Issue, EntryPoint
from mythril.analysis.swc_data import ARBITRARY_JUMP
from mythril.laser.ethereum.state.global_state import GlobalState

log = logging.getLogger(__name__)

DESCRIPTION = """

Search for jumps to arbitrary locations in the bytecode
"""


class ArbitraryJump(DetectionModule):
    """This module searches for JUMPs to an arbitrary instruction."""

    name = "Jump to an arbitrary bytecode location"
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
        if state.get_current_instruction()["address"] in self.cache:
            return
        self.issues.extend(self._analyze_state(state))

    @staticmethod
    def _analyze_state(state):
        """

        :param state:
        :return:
        """

        jump_dest = state.mstate.stack[-1]
        if jump_dest.symbolic is False:
            return []
        # Most probably the jump destination can have multiple locations in these circumstances
        try:
            transaction_sequence = get_transaction_sequence(
                state, state.world_state.constraints
            )
        except UnsatError:
            return []
        issue = Issue(
            contract=state.environment.active_account.contract_name,
            function_name=state.environment.active_function_name,
            address=state.get_current_instruction()["address"],
            swc_id=ARBITRARY_JUMP,
            title="Jump to an arbitrary instruction",
            severity="Medium",
            bytecode=state.environment.code.bytecode,
            description_head="The caller can jump to any point in the code.",
            description_tail="This can lead to unintended consequences."
            "Please avoid using low level code as much as possible",
            gas_used=(state.mstate.min_gas_used, state.mstate.max_gas_used),
            transaction_sequence=transaction_sequence,
        )
        return [issue]


detector = ArbitraryJump()
