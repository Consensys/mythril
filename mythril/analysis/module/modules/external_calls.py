"""This module contains the detection code for potentially insecure low-level
calls."""

from mythril.analysis import solver
from mythril.analysis.potential_issues import (
    PotentialIssue,
    get_potential_issues_annotation,
)
from mythril.analysis.swc_data import REENTRANCY
from mythril.laser.ethereum.state.constraints import Constraints
from mythril.laser.ethereum.transaction.symbolic import ACTORS
from mythril.analysis.module.base import DetectionModule, EntryPoint
from mythril.laser.smt import UGT, symbol_factory, Or, BitVec
from mythril.laser.ethereum.natives import PRECOMPILE_COUNT
from mythril.laser.ethereum.state.global_state import GlobalState
from mythril.exceptions import UnsatError
from copy import copy
import logging

log = logging.getLogger(__name__)

DESCRIPTION = """

Search for external calls with unrestricted gas to a user-specified address.

"""


def _is_precompile_call(global_state: GlobalState):
    to = global_state.mstate.stack[-2]  # type: BitVec
    constraints = copy(global_state.world_state.constraints)
    constraints += [
        Or(
            to < symbol_factory.BitVecVal(1, 256),
            to > symbol_factory.BitVecVal(PRECOMPILE_COUNT, 256),
        )
    ]

    try:
        solver.get_model(constraints)
        return False
    except UnsatError:
        return True


class ExternalCalls(DetectionModule):
    """This module searches for low level calls (e.g. call.value()) that
    forward all gas to the callee."""

    name = "External call to another contract"
    swc_id = REENTRANCY
    description = DESCRIPTION
    entry_point = EntryPoint.CALLBACK
    pre_hooks = ["CALL"]

    def _execute(self, state: GlobalState) -> None:
        """

        :param state:
        :return:
        """
        potential_issues = self._analyze_state(state)

        annotation = get_potential_issues_annotation(state)
        annotation.potential_issues.extend(potential_issues)

    def _analyze_state(self, state: GlobalState):
        """

        :param state:
        :return:
        """
        gas = state.mstate.stack[-1]
        to = state.mstate.stack[-2]

        address = state.get_current_instruction()["address"]

        try:
            constraints = Constraints(
                [UGT(gas, symbol_factory.BitVecVal(2300, 256)), to == ACTORS.attacker]
            )

            solver.get_transaction_sequence(
                state, constraints + state.world_state.constraints
            )

            description_head = "A call to a user-supplied address is executed."
            description_tail = (
                "An external message call to an address specified by the caller is executed. Note that "
                "the callee account might contain arbitrary code and could re-enter any function "
                "within this contract. Reentering the contract in an intermediate state may lead to "
                "unexpected behaviour. Make sure that no state modifications "
                "are executed after this call and/or reentrancy guards are in place."
            )

            issue = PotentialIssue(
                contract=state.environment.active_account.contract_name,
                function_name=state.environment.active_function_name,
                address=address,
                swc_id=REENTRANCY,
                title="External Call To User-Supplied Address",
                bytecode=state.environment.code.bytecode,
                severity="Low",
                description_head=description_head,
                description_tail=description_tail,
                constraints=constraints,
                detector=self,
            )

        except UnsatError:
            log.debug("[EXTERNAL_CALLS] No model found.")
            return []

        return [issue]


detector = ExternalCalls()
