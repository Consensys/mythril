"""This module contains the detection code for integer overflows and
underflows."""

import json
from typing import Dict
from mythril.analysis import solver
from mythril.analysis.report import Issue
from mythril.analysis.swc_data import INTEGER_OVERFLOW_AND_UNDERFLOW
from mythril.exceptions import UnsatError
from mythril.laser.ethereum.state.global_state import GlobalState
from mythril.analysis.modules.base import DetectionModule

from mythril.laser.smt import (
    BVAddNoOverflow,
    BVSubNoUnderflow,
    BVMulNoOverflow,
    BitVec,
    symbol_factory,
    Not,
    Expression,
)

import logging


log = logging.getLogger(__name__)


class OverUnderflowAnnotation:
    def __init__(self, overflowing_state: GlobalState, operator: str, constraint) -> None:
        self.overflowing_state = overflowing_state
        self.operator = operator
        self.constraint = constraint


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
            pre_hooks=["ADD", "MUL", "SUB", "SSTORE", "JUMPI"],
        )
        self._overflow_cache = {}  # type: Dict[int, bool]
        self._underflow_cache = {}  # type: Dict[int, bool]

    def reset_module(self):
        """
        Resets the module
        :return:
        """
        super().reset_module()
        self._overflow_cache = {}
        self._underflow_cache = {}

    def execute(self, state: GlobalState):
        """Executes analysis module for integer underflow and integer overflow.

        :param state: Statespace to analyse
        :return: Found issues
        """
        address = _get_address_from_state(state)
        has_overflow = self._overflow_cache.get(address, False)
        has_underflow = self._underflow_cache.get(address, False)
        if has_overflow or has_underflow:
            return
        if state.get_current_instruction()["opcode"] == "ADD":
            self._handle_add(state)
        elif state.get_current_instruction()["opcode"] == "MUL":
            self._handle_mul(state)
        elif state.get_current_instruction()["opcode"] == "SUB":
            self._handle_sub(state)
        elif state.get_current_instruction()["opcode"] == "SSTORE":
            self._handle_sstore(state)
        elif state.get_current_instruction()["opcode"] == "JUMPI":
            self._handle_jumpi(state)

    def _handle_add(self, state):
        stack = state.mstate.stack
        op0, op1 = (
            self._make_bitvec_if_not(stack, -1),
            self._make_bitvec_if_not(stack, -2),
        )
        c = Not(BVAddNoOverflow(op0, op1, False))

        # Check satisfiable
        model = self._try_constraints(state.node.constraints, [c])
        if model is None:
            return

        annotation = OverUnderflowAnnotation(state, "addition", c)
        op0.annotate(annotation)

    def _handle_mul(self, state):
        stack = state.mstate.stack
        op0, op1 = (
            self._make_bitvec_if_not(stack, -1),
            self._make_bitvec_if_not(stack, -2),
        )

        c = Not(BVMulNoOverflow(op0, op1, False))

        # Check satisfiable
        model = self._try_constraints(state.node.constraints, [c])
        if model is None:
            return

        annotation = OverUnderflowAnnotation(state, "multiplication", c)
        op0.annotate(annotation)

    def _handle_sub(self, state):
        stack = state.mstate.stack
        op0, op1 = (
            self._make_bitvec_if_not(stack, -1),
            self._make_bitvec_if_not(stack, -2),
        )
        c = Not(BVSubNoUnderflow(op0, op1, False))

        # Check satisfiable
        model = self._try_constraints(state.node.constraints, [c])
        if model is None:
            return

        annotation = OverUnderflowAnnotation(state, "subtraction", c)
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

    def _handle_sstore(self, state):
        stack = state.mstate.stack
        value = stack[-2]

        if not isinstance(value, Expression):
            return
        for annotation in value.annotations:
            if not isinstance(annotation, OverUnderflowAnnotation):
                continue

            _type = "Underflow" if annotation.operator == "subtraction" else "Overflow"
            ostate = annotation.overflowing_state
            node = ostate.node

            issue = Issue(
                contract=node.contract_name,
                function_name=node.function_name,
                address=ostate.get_current_instruction()["address"],
                swc_id=INTEGER_OVERFLOW_AND_UNDERFLOW,
                bytecode=ostate.environment.code.bytecode,
                title=self._get_title(_type),
                severity="High",
                description_head=self._get_description_head(annotation, _type),
                description_tail=self._get_description_tail(annotation, _type),
                gas_used=(state.mstate.min_gas_used, state.mstate.max_gas_used),
            )

            address = _get_address_from_state(ostate)

            if annotation.operator == "subtraction" and self._underflow_cache.get(
                address, False
            ):
                continue
            if annotation.operator != "subtraction" and self._overflow_cache.get(
                address, False
            ):
                continue

            try:

                transaction_sequence = solver.get_transaction_sequence(
                    state, node.constraints + [annotation.constraint]
                )

                issue.debug = json.dumps(transaction_sequence, indent=4)

            except UnsatError:
                continue
            if annotation.operator == "subtraction":
                self._underflow_cache[address] = True
            else:
                self._overflow_cache[address] = True

            self._issues.append(issue)

    def _handle_jumpi(self, state):
        stack = state.mstate.stack
        value = stack[-2]

        for annotation in value.annotations:
            if not isinstance(annotation, OverUnderflowAnnotation):
                continue
            ostate = annotation.overflowing_state
            node = ostate.node

            _type = "Underflow" if annotation.operator == "subtraction" else "Overflow"
            issue = Issue(
                contract=node.contract_name,
                function_name=node.function_name,
                address=ostate.get_current_instruction()["address"],
                swc_id=INTEGER_OVERFLOW_AND_UNDERFLOW,
                bytecode=ostate.environment.code.bytecode,
                title=self._get_title(_type),
                severity="High",
                description_head=self._get_description_head(annotation, _type),
                description_tail=self._get_description_tail(annotation, _type),
                gas_used=(state.mstate.min_gas_used, state.mstate.max_gas_used),
            )

            address = _get_address_from_state(ostate)

            if annotation.operator == "subtraction" and self._underflow_cache.get(
                address, False
            ):
                continue

            if annotation.operator != "subtraction" and self._overflow_cache.get(
                address, False
            ):
                continue

            try:

                transaction_sequence = solver.get_transaction_sequence(
                    state, node.constraints + [annotation.constraint]
                )

                issue.debug = json.dumps(transaction_sequence, indent=4)

            except UnsatError:
                continue

            if annotation.operator == "subtraction":
                self._underflow_cache[address] = True
            else:
                self._overflow_cache[address] = True
            self._issues.append(issue)

    @staticmethod
    def _try_constraints(constraints, new_constraints):
        """
        Tries new constraints
        :return Model if satisfiable otherwise None
        """
        try:
            return solver.get_model(constraints + new_constraints)
        except UnsatError:
            return None


detector = IntegerOverflowUnderflowModule()


def _get_address_from_state(state):
    return state.get_current_instruction()["address"]
