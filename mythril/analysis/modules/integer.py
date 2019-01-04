"""This module contains the detection code for integer overflows and
underflows."""

import json

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
    def __init__(self, overflowing_state: GlobalState, operator: str, constraint):
        self.overflowing_state = overflowing_state
        self.operator = operator
        self.constraint = constraint


class IntegerOverflowUnderflowModule(DetectionModule):
    """This module searches for integer over- and underflows."""

    def __init__(self):
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

    def execute(self, state: GlobalState):
        """Executes analysis module for integer underflow and integer overflow.

        :param state: Statespace to analyse
        :return: Found issues
        """
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

            description_head = "The binary {} can {}.".format(
                annotation.operator, _type.lower()
            )

            description_tail = (
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

            issue = Issue(
                contract=node.contract_name,
                function_name=node.function_name,
                address=ostate.get_current_instruction()["address"],
                swc_id=INTEGER_OVERFLOW_AND_UNDERFLOW,
                bytecode=ostate.environment.code.bytecode,
                title="Integer {}".format(_type),
                severity="High",
                description_head=description_head,
                description_tail=description_tail,
                gas_used=(state.mstate.min_gas_used, state.mstate.max_gas_used),
            )

            try:

                transaction_sequence =  olver.get_transaction_sequence(
                        state, node.constraints + [annotation.constraint]
                    )

                issue.debug = json.dumps(transaction_sequence, indent=4)

            except UnsatError:
                return
            self._issues.append(issue)

    def _handle_jumpi(self, state):
        stack = state.mstate.stack
        value = stack[-2]

        for annotation in value.annotations:
            if not isinstance(annotation, OverUnderflowAnnotation):
                continue
            ostate = annotation.overflowing_state
            node = ostate.node

            description_tail = "The binary {} operation can result in an integer overflow.\n".format(
                annotation.operator
            )
            title = (
                "Integer Underflow"
                if annotation.operator == "subtraction"
                else "Integer Overflow"
            )

            issue = Issue(
                contract=node.contract_name,
                function_name=node.function_name,
                address=ostate.get_current_instruction()["address"],
                swc_id=INTEGER_OVERFLOW_AND_UNDERFLOW,
                bytecode=ostate.environment.code.bytecode,
                title=title,
                severity="High",
                description_head="The {} can overflow.".format(annotation.operator),
                description_tail=description_tail,
                gas_used=(state.mstate.min_gas_used, state.mstate.max_gas_used),
            )

            try:

                transaction_sequence = solver.get_transaction_sequence(
                    state, node.constraints + [annotation.constraint]
                )

                issue.debug = json.dumps(transaction_sequence, indent=4)

            except UnsatError:
                return
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
