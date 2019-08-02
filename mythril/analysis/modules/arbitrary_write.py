"""This module contains the detection code for unauthorized ether
withdrawal."""
import logging
from copy import copy
from typing import List, Tuple
from mythril.analysis import solver
from mythril.analysis.analysis_module_helpers import get_or_create_annotation
from mythril.analysis.modules.base import DetectionModule

from mythril.analysis.report import Issue
from mythril.analysis.swc_data import WRITE_TO_ARBITRARY_STORAGE
from mythril.exceptions import UnsatError
from mythril.laser.ethereum.state.annotation import StateAnnotation
from mythril.laser.ethereum.state.global_state import GlobalState
from mythril.laser.smt import symbol_factory, BitVecFunc

log = logging.getLogger(__name__)

DESCRIPTION = """

Search for cases where Ether can be withdrawn to a user-specified address.

An issue is reported if:

- The transaction sender does not match contract creator;
- The sender address can be chosen arbitrarily;
- The receiver address is identical to the sender address;
- The sender can withdraw *more* than the total amount they sent over all transactions.

"""


class AribtraryWriteAnnotation(StateAnnotation):
    def __init__(self) -> None:
        self.storage_write_slots = []  # type: List[Tuple[int, int]]

    def __copy__(self):
        result = AribtraryWriteAnnotation()
        result.storage_write_slots = copy(self.storage_write_slots)
        return result


class ArbitraryStorage(DetectionModule):
    """This module search for cases where Ether can be withdrawn to a user-
    specified address."""

    def __init__(self):
        """"""
        super().__init__(
            name="Arbitrary Storage Write",
            swc_id=WRITE_TO_ARBITRARY_STORAGE,
            description=DESCRIPTION,
            entrypoint="callback",
            pre_hooks=["STOP", "RETURN", "SSTORE"],
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
        if state.get_current_instruction()["address"] in self._cache:
            return
        issues = self._analyze_state(state)
        for issue in issues:
            self._cache.add(issue.address)
        self._issues.extend(issues)

    @staticmethod
    def _analyze_state(state):
        """

        :param state:
        :return:
        """
        annotation = get_or_create_annotation(
            state, AribtraryWriteAnnotation
        )  # type: AribtraryWriteAnnotation
        instruction = state.get_current_instruction()

        if instruction["opcode"] == "SSTORE":
            write_slot = state.mstate.stack[-1]
            annotation.storage_write_slots.append((write_slot, instruction["address"]))
            return []

        issues = []
        for write_slot, address in annotation.storage_write_slots:
            constraints = []

            # For maps
            if (
                isinstance(write_slot, BitVecFunc)
                and write_slot.func_name == "keccak256"
                and not isinstance(write_slot.input_, BitVecFunc)
            ):
                constraints.append(
                    write_slot.input_ == symbol_factory.BitVecVal(1324577524, 256)
                )
            else:
                # Non maps
                constraints.append(
                    write_slot == symbol_factory.BitVecVal(324345425435, 256)
                )

            constraints = state.mstate.constraints + constraints
            try:

                transaction_sequence = solver.get_transaction_sequence(
                    state, constraints
                )

                issue = Issue(
                    contract=state.environment.active_account.contract_name,
                    function_name=state.environment.active_function_name,
                    address=address,
                    swc_id=WRITE_TO_ARBITRARY_STORAGE,
                    title="Write to an arbitrary storage slot",
                    severity="Medium",
                    bytecode=state.environment.code.bytecode,
                    description_head="Any storage slot can be written by the caller.",
                    description_tail="The caller can write a value into an arbitrary storage slot."
                    + " This can lead to unintended consequences.",
                    transaction_sequence=transaction_sequence,
                    gas_used=(state.mstate.min_gas_used, state.mstate.max_gas_used),
                )
                issues.append(issue)
            except UnsatError:
                log.debug("No model found")
                continue

        return issues


detector = ArbitraryStorage()
