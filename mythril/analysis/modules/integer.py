"""This module contains the detection code for integer overflows and
underflows."""

import json

from math import log2, ceil
from typing import cast, List
from mythril.analysis import solver
from mythril.analysis.report import Issue
from mythril.analysis.swc_data import INTEGER_OVERFLOW_AND_UNDERFLOW
from mythril.exceptions import UnsatError
from mythril.laser.ethereum.state.global_state import GlobalState
from mythril.laser.ethereum.util import get_concrete_int
from mythril.laser.ethereum.state.annotation import StateAnnotation
from mythril.analysis.modules.base import DetectionModule
from copy import copy

from mythril.laser.smt import (
    BVAddNoOverflow,
    BVSubNoUnderflow,
    BVMulNoOverflow,
    BitVec,
    symbol_factory,
    Not,
    Expression,
    Bool,
    And,
)

import logging

log = logging.getLogger(__name__)

DISABLE_EFFECT_CHECK = True


class OverUnderflowAnnotation:
    """ Symbol Annotation used if a BitVector can overflow"""

    def __init__(
        self, overflowing_state: GlobalState, operator: str, constraint: Bool
    ) -> None:
        self.overflowing_state = overflowing_state
        self.operator = operator
        self.constraint = constraint


class OverUnderflowStateAnnotation(StateAnnotation):
    """ State Annotation used if an overflow is both possible and used in the annotated path"""

    def __init__(self) -> None:
        self.overflowing_state_annotations = []  # type: List[OverUnderflowAnnotation]
        self.ostates_seen = []  # type: List[GlobalState]

    def __copy__(self):
        new_annotation = OverUnderflowStateAnnotation()

        new_annotation.overflowing_state_annotations = copy(
            self.overflowing_state_annotations
        )
        new_annotation.ostates_seen = copy(self.ostates_seen)

        return new_annotation


class IntegerOverflowUnderflowModule(DetectionModule):
    """This module searches for integer over- and underflows."""

    def __init__(self) -> None:
        """"""
        super().__init__(
            name="Integer Overflow and Underflow",
            swc_id=INTEGER_OVERFLOW_AND_UNDERFLOW,
            description=(
                "For every SUB instruction, check if there's a possible state "
                "where op1 > op0. For every ADD, MUL instruction, check if "
                "there's a possible state where op1 + op0 > 2^32 - 1"
            ),
            entrypoint="callback",
            pre_hooks=["ADD", "MUL", "EXP", "SUB", "SSTORE", "JUMPI", "STOP", "RETURN"],
        )

    def reset_module(self):
        """
        Resets the module
        :return:
        """
        super().reset_module()

    def _execute(self, state: GlobalState) -> None:
        """Executes analysis module for integer underflow and integer overflow.

        :param state: Statespace to analyse
        :return: Found issues
        """

        opcode = state.get_current_instruction()["opcode"]

        funcs = {
            "ADD": [self._handle_add],
            "SUB": [self._handle_sub],
            "MUL": [self._handle_mul],
            "SSTORE": [self._handle_sstore],
            "JUMPI": [self._handle_jumpi],
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
        if op0.symbolic and op1.symbolic:
            constraint = And(
                op1 > symbol_factory.BitVecVal(256, 256),
                op0 > symbol_factory.BitVecVal(1, 256),
            )
        elif op1.symbolic:
            if op0.value < 2:
                return
            constraint = op1 >= symbol_factory.BitVecVal(
                ceil(256 / log2(op0.value)), 256
            )
        elif op0.symbolic:
            if op1.value == 0:
                return
            constraint = op0 >= symbol_factory.BitVecVal(
                2 ** ceil(256 / op1.value), 256
            )
        else:
            constraint = op0.value ** op1.value >= 2 ** 256

        annotation = OverUnderflowAnnotation(state, "exponentiation", constraint)
        op0.annotate(annotation)

    @staticmethod
    def _make_bitvec_if_not(stack, index):
        value = stack[index]
        if isinstance(value, BitVec):
            return value
        stack[index] = symbol_factory.BitVecVal(value, 256)
        return stack[index]

    @staticmethod
    def _get_description_head(annotation, _type):
        return "The binary {} can {}.".format(annotation.operator, _type.lower())

    @staticmethod
    def _get_description_tail(annotation, _type):

        return (
            "The operands of the {} operation are not sufficiently constrained. "
            "The {} could therefore result in an integer {}. Prevent the {} by checking inputs "
            "or ensure sure that the {} is caught by an assertion.".format(
                annotation.operator,
                annotation.operator,
                _type.lower(),
                _type.lower(),
                _type.lower(),
            )
        )

    @staticmethod
    def _get_title(_type):
        return "Integer {}".format(_type)

    @staticmethod
    def _handle_sstore(state: GlobalState) -> None:

        stack = state.mstate.stack
        value = stack[-2]

        if not isinstance(value, Expression):
            return

        state_annotations = cast(
            List[OverUnderflowStateAnnotation],
            list(state.get_annotations(OverUnderflowStateAnnotation)),
        )

        if len(state_annotations) == 0:
            state_annotation = OverUnderflowStateAnnotation()
            state.annotate(state_annotation)
        else:
            state_annotation = state_annotations[0]

        for annotation in value.annotations:
            if (
                not isinstance(annotation, OverUnderflowAnnotation)
                or annotation.overflowing_state in state_annotation.ostates_seen
            ):
                continue

            state_annotation.overflowing_state_annotations.append(annotation)
            state_annotation.ostates_seen.append(annotation.overflowing_state)

    @staticmethod
    def _handle_jumpi(state):

        stack = state.mstate.stack
        value = stack[-2]

        state_annotations = cast(
            List[OverUnderflowStateAnnotation],
            list(state.get_annotations(OverUnderflowStateAnnotation)),
        )

        if len(state_annotations) == 0:
            state_annotation = OverUnderflowStateAnnotation()
            state.annotate(state_annotation)
        else:
            state_annotation = state_annotations[0]

        for annotation in value.annotations:
            if (
                not isinstance(annotation, OverUnderflowAnnotation)
                or annotation.overflowing_state in state_annotation.ostates_seen
            ):
                continue

            state_annotation.overflowing_state_annotations.append(annotation)
            state_annotation.ostates_seen.append(annotation.overflowing_state)

    @staticmethod
    def _handle_return(state: GlobalState) -> None:
        """
        Adds all the annotations into the state which correspond to the
        locations in the memory returned by RETURN opcode.
        :param state: The Global State
        """
        stack = state.mstate.stack
        try:
            offset, length = get_concrete_int(stack[-1]), get_concrete_int(stack[-2])
        except TypeError:
            return

        """ TODO: Rewrite this
        for element in state.mstate.memory[offset : offset + length]:
            if not isinstance(element, Expression):
                continue
            for annotation in element.annotations:
                if isinstance(annotation, OverUnderflowAnnotation):
                    
                    state.annotate(
                        OverUnderflowStateAnnotation(
                            annotation.overflowing_state,
                            annotation.operator,
                            annotation.constraint,
                        )
                    )
        """

    def _handle_transaction_end(self, state: GlobalState) -> None:

        state_annotations = cast(
            List[OverUnderflowStateAnnotation],
            list(state.get_annotations(OverUnderflowStateAnnotation)),
        )

        if len(state_annotations) == 0:
            return

        annotations = state_annotations[0].overflowing_state_annotations

        for annotation in annotations:

            ostate = annotation.overflowing_state

            try:
                # This check can be disabled if the constraints are to difficult for z3 to solve
                # within any reasonable time.
                if DISABLE_EFFECT_CHECK:
                    constraints = ostate.mstate.constraints + [annotation.constraint]
                else:
                    constraints = state.mstate.constraints + [annotation.constraint]

                transaction_sequence = solver.get_transaction_sequence(
                    state, constraints
                )

            except UnsatError:
                continue

            _type = "Underflow" if annotation.operator == "subtraction" else "Overflow"
            issue = Issue(
                contract=ostate.environment.active_account.contract_name,
                function_name=ostate.environment.active_function_name,
                address=ostate.get_current_instruction()["address"],
                swc_id=INTEGER_OVERFLOW_AND_UNDERFLOW,
                bytecode=ostate.environment.code.bytecode,
                title=self._get_title(_type),
                severity="High",
                description_head=self._get_description_head(annotation, _type),
                description_tail=self._get_description_tail(annotation, _type),
                gas_used=(state.mstate.min_gas_used, state.mstate.max_gas_used),
            )

            issue.debug = json.dumps(transaction_sequence, indent=4)

            self._issues.append(issue)

    @staticmethod
    def _try_constraints(constraints, new_constraints):
        """ Tries new constraints
        :return Model if satisfiable otherwise None
        """
        try:
            return solver.get_model(constraints + new_constraints)
        except UnsatError:
            return None


detector = IntegerOverflowUnderflowModule()
