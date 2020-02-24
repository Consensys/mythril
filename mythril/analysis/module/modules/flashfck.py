"""This module contains the detection code for arbitrary storage write."""
import logging
from mythril.analysis.modules.base import DetectionModule

from mythril.analysis.report import Issue

from mythril.analysis.swc_data import WRITE_TO_ARBITRARY_STORAGE
from mythril.laser.ethereum.state.global_state import GlobalState
from mythril.laser.smt import symbol_factory

log = logging.getLogger(__name__)

DESCRIPTION = """

Search for arbitrage opportunities with large capital
"""


class FlashFck(DetectionModule):
    """This module searches for flash loan arbitrage opportunities."""

    def __init__(self):
        """"""
        super().__init__(
            name="Flash Loan Attack",
            swc_id=0,
            description=DESCRIPTION,
            entrypoint="post",
        )

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
        issues = self._analyze_state(state)


    def _analyze_state(self, state):
        """

        :param state:
        :return:
        """

        write_slot = state.mstate.stack[-1]
        constraints = state.world_state.constraints + [
            write_slot == symbol_factory.BitVecVal(324345425435, 256)
        ]

        issue = Issue(
            contract=state.environment.active_account.contract_name,
            function_name=state.environment.active_function_name,
            address=state.get_current_instruction()["address"],
            swc_id=WRITE_TO_ARBITRARY_STORAGE,
            title="Write to an arbitrary storage slot",
            severity="High",
            bytecode=state.environment.code.bytecode,
            description_head="Any storage slot can be written by the caller.",
            description_tail="The attacker can modify any value in the storage."
            + " This can lead to unintended consequences.",
            detector=self,
        )
        return [issue]


detector = FlashFck()
