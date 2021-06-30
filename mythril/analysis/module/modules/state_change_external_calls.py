from mythril.analysis.potential_issues import (
    PotentialIssue,
    get_potential_issues_annotation,
)
from mythril.analysis.swc_data import REENTRANCY
from mythril.analysis.module.base import DetectionModule, EntryPoint
from mythril.laser.ethereum.state.constraints import Constraints
from mythril.laser.smt import symbol_factory, UGT, BitVec, Or
from mythril.laser.ethereum.state.global_state import GlobalState
from mythril.laser.ethereum.state.annotation import StateAnnotation
from mythril.analysis import solver
from mythril.exceptions import UnsatError
from typing import List, cast, Optional
from copy import copy

import logging

log = logging.getLogger(__name__)

DESCRIPTION = """

Check whether the account state is accesses after the execution of an external call
"""

CALL_LIST = ["CALL", "DELEGATECALL", "CALLCODE"]
STATE_READ_WRITE_LIST = ["SSTORE", "SLOAD", "CREATE", "CREATE2"]


class StateChangeCallsAnnotation(StateAnnotation):
    def __init__(self, call_state: GlobalState, user_defined_address: bool) -> None:
        self.call_state = call_state
        self.state_change_states = []  # type: List[GlobalState]
        self.user_defined_address = user_defined_address

    def __copy__(self):
        new_annotation = StateChangeCallsAnnotation(
            self.call_state, self.user_defined_address
        )
        new_annotation.state_change_states = self.state_change_states[:]
        return new_annotation

    def get_issue(
        self, global_state: GlobalState, detector: DetectionModule
    ) -> Optional[PotentialIssue]:
        if not self.state_change_states:
            return None
        constraints = Constraints()
        gas = self.call_state.mstate.stack[-1]
        to = self.call_state.mstate.stack[-2]
        constraints += [
            UGT(gas, symbol_factory.BitVecVal(2300, 256)),
            Or(
                to > symbol_factory.BitVecVal(16, 256),
                to == symbol_factory.BitVecVal(0, 256),
            ),
        ]
        if self.user_defined_address:
            constraints += [to == 0xDEADBEEFDEADBEEFDEADBEEFDEADBEEFDEADBEEF]

        try:
            solver.get_transaction_sequence(
                global_state, constraints + global_state.world_state.constraints
            )
        except UnsatError:
            return None

        severity = "Medium" if self.user_defined_address else "Low"
        address = global_state.get_current_instruction()["address"]
        logging.debug(
            "[EXTERNAL_CALLS] Detected state changes at addresses: {}".format(address)
        )
        read_or_write = "Write to"
        if global_state.get_current_instruction()["opcode"] == "SLOAD":
            read_or_write = "Read of"
        address_type = "user defined" if self.user_defined_address else "fixed"
        description_head = "{} persistent state following external call".format(
            read_or_write
        )
        description_tail = (
            "The contract account state is accessed after an external call to a {} address. "
            "To prevent reentrancy issues, consider accessing the state only before the call, especially if the callee is untrusted. "
            "Alternatively, a reentrancy lock can be used to prevent "
            "untrusted callees from re-entering the contract in an intermediate state.".format(
                address_type
            )
        )

        return PotentialIssue(
            contract=global_state.environment.active_account.contract_name,
            function_name=global_state.environment.active_function_name,
            address=address,
            title="State access after external call",
            severity=severity,
            description_head=description_head,
            description_tail=description_tail,
            swc_id=REENTRANCY,
            bytecode=global_state.environment.code.bytecode,
            constraints=constraints,
            detector=detector,
        )


class StateChangeAfterCall(DetectionModule):
    """This module searches for state change after low level calls (e.g. call.value()) that
    forward gas to the callee."""

    name = "State change after an external call"
    swc_id = REENTRANCY
    description = DESCRIPTION
    entry_point = EntryPoint.CALLBACK
    pre_hooks = CALL_LIST + STATE_READ_WRITE_LIST

    def _execute(self, state: GlobalState) -> None:
        if state.get_current_instruction()["address"] in self.cache:
            return
        issues = self._analyze_state(state)

        annotation = get_potential_issues_annotation(state)
        annotation.potential_issues.extend(issues)

    @staticmethod
    def _add_external_call(global_state: GlobalState) -> None:
        gas = global_state.mstate.stack[-1]
        to = global_state.mstate.stack[-2]
        try:
            constraints = copy(global_state.world_state.constraints)
            solver.get_model(
                constraints
                + [
                    UGT(gas, symbol_factory.BitVecVal(2300, 256)),
                    Or(
                        to > symbol_factory.BitVecVal(16, 256),
                        to == symbol_factory.BitVecVal(0, 256),
                    ),
                ]
            )

            # Check whether we can also set the callee address
            try:
                constraints += [to == 0xDEADBEEFDEADBEEFDEADBEEFDEADBEEFDEADBEEF]
                solver.get_model(constraints)

                global_state.annotate(StateChangeCallsAnnotation(global_state, True))
            except UnsatError:
                global_state.annotate(StateChangeCallsAnnotation(global_state, False))
        except UnsatError:
            pass

    def _analyze_state(self, global_state: GlobalState) -> List[PotentialIssue]:

        annotations = cast(
            List[StateChangeCallsAnnotation],
            list(global_state.get_annotations(StateChangeCallsAnnotation)),
        )
        op_code = global_state.get_current_instruction()["opcode"]

        if len(annotations) == 0 and op_code in STATE_READ_WRITE_LIST:
            return []

        if op_code in STATE_READ_WRITE_LIST:
            for annotation in annotations:
                annotation.state_change_states.append(global_state)

        # Record state changes following from a transfer of ether
        if op_code in CALL_LIST:
            value = global_state.mstate.stack[-3]  # type: BitVec
            if StateChangeAfterCall._balance_change(value, global_state):
                for annotation in annotations:
                    annotation.state_change_states.append(global_state)

        # Record external calls
        if op_code in CALL_LIST:
            StateChangeAfterCall._add_external_call(global_state)

        # Check for vulnerabilities
        vulnerabilities = []
        for annotation in annotations:
            if not annotation.state_change_states:
                continue
            issue = annotation.get_issue(global_state, self)
            if issue:
                vulnerabilities.append(issue)
        return vulnerabilities

    @staticmethod
    def _balance_change(value: BitVec, global_state: GlobalState) -> bool:
        if not value.symbolic:
            assert value.value is not None
            return value.value > 0

        else:
            constraints = copy(global_state.world_state.constraints)

            try:
                solver.get_model(
                    constraints + [value > symbol_factory.BitVecVal(0, 256)]
                )
                return True
            except UnsatError:
                return False


detector = StateChangeAfterCall()
