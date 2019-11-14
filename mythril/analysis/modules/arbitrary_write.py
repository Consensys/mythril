"""This module contains the detection code for arbitrary storage write."""
import logging
from mythril.analysis.modules.base import DetectionModule
from mythril.analysis.potential_issues import (
    get_potential_issues_annotation,
    PotentialIssue,
)

from mythril.analysis.swc_data import WRITE_TO_ARBITRARY_STORAGE
from mythril.laser.ethereum.state.global_state import GlobalState
from mythril.laser.smt import symbol_factory

log = logging.getLogger(__name__)

DESCRIPTION = """

Search for any writes to an arbitrary storage slot
"""


class ArbitraryStorage(DetectionModule):
    """This module searches for a feasible write to an arbitrary storage slot."""

    def __init__(self):
        """"""
        super().__init__(
            name="Arbitrary Storage Write",
            swc_id=WRITE_TO_ARBITRARY_STORAGE,
            description=DESCRIPTION,
            entrypoint="callback",
            pre_hooks=["SSTORE"],
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
        potential_issues = self._analyze_state(state)

        annotation = get_potential_issues_annotation(state)
        annotation.potential_issues.extend(potential_issues)

    def _analyze_state(self, state):
        """

        :param state:
        :return:
        """

        write_slot = state.mstate.stack[-1]
        constraints = state.world_state.constraints + [
            write_slot == symbol_factory.BitVecVal(324345425435, 256)
        ]

        potential_issue = PotentialIssue(
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
            constraints=constraints,
        )
        return [potential_issue]


detector = ArbitraryStorage()
