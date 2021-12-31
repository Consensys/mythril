"""This module contains the detection code for integer overflows and
underflows."""

from math import log2, ceil
from typing import cast, List, Set
from mythril.analysis import solver
from mythril.analysis.report import Issue
from mythril.analysis.swc_data import INTEGER_OVERFLOW_AND_UNDERFLOW
from mythril.exceptions import UnsatError
from mythril.laser.ethereum.state.global_state import GlobalState
from mythril.laser.ethereum.state.annotation import StateAnnotation
from mythril.analysis.module.base import DetectionModule, EntryPoint
from copy import copy

from mythril.laser.smt import (
    BVAddNoOverflow,
    BVSubNoUnderflow,
    BVMulNoOverflow,
    BitVec,
    If,
    symbol_factory,
    Not,
    Expression,
    Bool,
    And,
)

import logging

log = logging.getLogger(__name__)


class OverUnderflowAnnotation:
    """Symbol Annotation used if a BitVector can overflow"""

    def __init__(
        self, overflowing_state: GlobalState, operator: str, constraint: Bool
    ) -> None:
        self.overflowing_state = overflowing_state
        self.operator = operator
        self.constraint = constraint

    def __deepcopy__(self, memodict={}):
        new_annotation = copy(self)
        return new_annotation


class OverUnderflowStateAnnotation(StateAnnotation):
    """State Annotation used if an overflow is both possible and used in the annotated path"""

    def __init__(self) -> None:
        self.overflowing_state_annotations = set()  # type: Set[OverUnderflowAnnotation]

    def __copy__(self):
        new_annotation = OverUnderflowStateAnnotation()

        new_annotation.overflowing_state_annotations = copy(
            self.overflowing_state_annotations
        )

        return new_annotation


class IntegerArithmetics(DetectionModule):
    """This module searches for integer over- and underflows."""

    name = "Integer overflow or underflow"
    swc_id = INTEGER_OVERFLOW_AND_UNDERFLOW
    description = (
        "For every SUB instruction, check if there's a possible state "
        "where op1 > op0. For every ADD, MUL instruction, check if "
        "there's a possible state where op1 + op0 > 2^32 - 1"
    )
    entry_point = EntryPoint.CALLBACK
    pre_hooks = [
        "ADD",
        "MUL",
        "EXP",
        "SUB",
        "SSTORE",
        "JUMPI",
        "STOP",
        "RETURN",
        "CALL",
    ]

    def __init__(self) -> None:
        """
        Cache satisfiability of overflow constraints
        """
        super().__init__()

        self._ostates_satisfiable = set()  # type: Set[GlobalState]
        self._ostates_unsatisfiable = set()  # type: Set[GlobalState]

    def reset_module(self):
        """
        Resets the module
        :return:
        """
        super().reset_module()
        self._ostates_satisfiable = set()
        self._ostates_unsatisfiable = set()

    def _execute(self, state: GlobalState) -> None:
        """Executes analysis module for integer underflow and integer overflow.

        :param state: Statespace to analyse
        :return: Found issues
        """

        address = _get_address_from_state(state)

        if address in self.cache:
            return

        opcode = state.get_current_instruction()["opcode"]

        funcs = {
            "ADD": [self._handle_add],
            "SUB": [self._handle_sub],
            "MUL": [self._handle_mul],
            "SSTORE": [self._handle_sstore],
            "JUMPI": [self._handle_jumpi],
            "CALL": [self._handle_call],
            "RETURN": [self._handle_return, self._handle_transaction_end],
            "STOP": [self._handle_transaction_end],
            "EXP": [self._handle_exp],
        }
        for func in funcs[opcode]:
            func(state)

    def _get_args(self, state):
        stack = state.mstate.stack
        op0, op1 = (
            self._make_bitvec_if_not(stack, -1),
            self._make_bitvec_if_not(stack, -2),
        )
        return op0, op1

    def _handle_add(self, state):
        op0, op1 = self._get_args(state)
        c = Not(BVAddNoOverflow(op0, op1, False))

        annotation = OverUnderflowAnnotation(state, "addition", c)
        op0.annotate(annotation)

    def _handle_mul(self, state):
        op0, op1 = self._get_args(state)
        c = Not(BVMulNoOverflow(op0, op1, False))

        annotation = OverUnderflowAnnotation(state, "multiplication", c)
        op0.annotate(annotation)

    def _handle_sub(self, state):
        op0, op1 = self._get_args(state)
        c = Not(BVSubNoUnderflow(op0, op1, False))

        annotation = OverUnderflowAnnotation(state, "subtraction", c)
        op0.annotate(annotation)

    def _handle_exp(self, state):
        op0, op1 = self._get_args(state)

        if (op1.symbolic is False and op1.value == 0) or (
            op0.symbolic is False and op0.value < 2
        ):
            return
        if op0.symbolic and op1.symbolic:
            constraint = And(
                op1 > symbol_factory.BitVecVal(256, 256),
                op0 > symbol_factory.BitVecVal(1, 256),
            )
        elif op0.symbolic:
            constraint = op0 >= symbol_factory.BitVecVal(
                2 ** ceil(256 / op1.value), 256
            )
        else:
            constraint = op1 >= symbol_factory.BitVecVal(
                ceil(256 / log2(op0.value)), 256
            )

        annotation = OverUnderflowAnnotation(state, "exponentiation", constraint)
        op0.annotate(annotation)

    @staticmethod
    def _make_bitvec_if_not(stack, index):
        value = stack[index]
        if isinstance(value, BitVec):
            return value
        if isinstance(value, Bool):
            return If(value, 1, 0)
        stack[index] = symbol_factory.BitVecVal(value, 256)
        return stack[index]

    @staticmethod
    def _get_title(_type):
        return "Integer {}".format(_type)

    @staticmethod
    def _handle_sstore(state: GlobalState) -> None:

        stack = state.mstate.stack
        value = stack[-2]

        if not isinstance(value, Expression):
            return

        state_annotation = _get_overflowunderflow_state_annotation(state)

        for annotation in value.annotations:
            if isinstance(annotation, OverUnderflowAnnotation):
                state_annotation.overflowing_state_annotations.add(annotation)

    @staticmethod
    def _handle_jumpi(state):

        stack = state.mstate.stack
        value = stack[-2]

        state_annotation = _get_overflowunderflow_state_annotation(state)

        for annotation in value.annotations:
            if isinstance(annotation, OverUnderflowAnnotation):
                state_annotation.overflowing_state_annotations.add(annotation)

    @staticmethod
    def _handle_call(state):

        stack = state.mstate.stack
        value = stack[-3]

        state_annotation = _get_overflowunderflow_state_annotation(state)

        for annotation in value.annotations:
            if isinstance(annotation, OverUnderflowAnnotation):
                state_annotation.overflowing_state_annotations.add(annotation)

    @staticmethod
    def _handle_return(state: GlobalState) -> None:
        """
        Adds all the annotations into the state which correspond to the
        locations in the memory returned by RETURN opcode.
        :param state: The Global State
        """

        stack = state.mstate.stack
        offset, length = stack[-1], stack[-2]

        state_annotation = _get_overflowunderflow_state_annotation(state)

        for element in state.mstate.memory[offset : offset + length]:

            if not isinstance(element, Expression):
                continue

            for annotation in element.annotations:
                if isinstance(annotation, OverUnderflowAnnotation):
                    state_annotation.overflowing_state_annotations.add(annotation)

    def _handle_transaction_end(self, state: GlobalState) -> None:

        state_annotation = _get_overflowunderflow_state_annotation(state)

        for annotation in state_annotation.overflowing_state_annotations:

            ostate = annotation.overflowing_state

            if ostate in self._ostates_unsatisfiable:
                continue

            if ostate not in self._ostates_satisfiable:
                try:
                    constraints = ostate.world_state.constraints + [
                        annotation.constraint
                    ]
                    solver.get_model(constraints)
                    self._ostates_satisfiable.add(ostate)
                except:
                    self._ostates_unsatisfiable.add(ostate)
                    continue

            log.debug(
                "Checking overflow in {} at transaction end address {}, ostate address {}".format(
                    state.get_current_instruction()["opcode"],
                    state.get_current_instruction()["address"],
                    ostate.get_current_instruction()["address"],
                )
            )

            try:

                constraints = state.world_state.constraints + [annotation.constraint]
                transaction_sequence = solver.get_transaction_sequence(
                    state, constraints
                )
            except UnsatError:
                continue

            description_head = "The arithmetic operator can {}.".format(
                "underflow" if annotation.operator == "subtraction" else "overflow"
            )
            description_tail = "It is possible to cause an integer overflow or underflow in the arithmetic operation. "
            "Prevent this by constraining inputs using the require() statement or use the OpenZeppelin "
            "SafeMath library for integer arithmetic operations. "
            "Refer to the transaction trace generated for this issue to reproduce the issue."

            issue = Issue(
                contract=ostate.environment.active_account.contract_name,
                function_name=ostate.environment.active_function_name,
                address=ostate.get_current_instruction()["address"],
                swc_id=INTEGER_OVERFLOW_AND_UNDERFLOW,
                bytecode=ostate.environment.code.bytecode,
                title="Integer Arithmetic Bugs",
                severity="High",
                description_head=description_head,
                description_tail=description_tail,
                gas_used=(state.mstate.min_gas_used, state.mstate.max_gas_used),
                transaction_sequence=transaction_sequence,
            )

            address = _get_address_from_state(ostate)
            self.cache.add(address)
            self.issues.append(issue)


detector = IntegerArithmetics()


def _get_address_from_state(state):
    return state.get_current_instruction()["address"]


def _get_overflowunderflow_state_annotation(
    state: GlobalState,
) -> OverUnderflowStateAnnotation:
    state_annotations = cast(
        List[OverUnderflowStateAnnotation],
        list(state.get_annotations(OverUnderflowStateAnnotation)),
    )

    if len(state_annotations) == 0:
        state_annotation = OverUnderflowStateAnnotation()
        state.annotate(state_annotation)
        return state_annotation
    else:
        return state_annotations[0]
