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
    def __init__(self):
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
        self.overflow_cache = {}
        self.underflow_cache = {}
        self._issues = []

    @property
    def issues(self):
        return self._issues

    def execute(self, state: GlobalState):
        address = state.get_current_instruction()["address"]
        has_overflow = self.overflow_cache.get(address, False)
        has_underflow = self.underflow_cache.get(address, False)
        if state.get_current_instruction()["opcode"] == "ADD" and not has_overflow:
            self._handle_add(state)
        elif state.get_current_instruction()["opcode"] == "MUL" and not has_overflow:
            self._handle_mul(state)
        elif state.get_current_instruction()["opcode"] == "SUB" and not has_underflow:
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

        annotation = OverUnderflowAnnotation(state, "add", c)
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

        annotation = OverUnderflowAnnotation(state, "multiply", c)
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

            title = (
                "Integer Underflow"
                if annotation.operator == "subtraction"
                else "Integer Overflow"
            )
            ostate = annotation.overflowing_state
            node = ostate.node
            issue = Issue(
                contract=node.contract_name,
                function_name=node.function_name,
                address=ostate.get_current_instruction()["address"],
                swc_id=INTEGER_OVERFLOW_AND_UNDERFLOW,
                bytecode=ostate.environment.code.bytecode,
                title=title,
                _type="Warning",
                gas_used=(state.mstate.min_gas_used, state.mstate.max_gas_used),
            )

            issue.description = "This binary {} operation can result in {}.\n".format(
                annotation.operator, title.lower()
            )
            address = ostate.get_current_instruction()["address"]

            if annotation.operator == "subtraction" and self.underflow_cache.get(
                address, False
            ):
                return
            if annotation.operator != "subtraction" and self.overflow_cache.get(
                address, False
            ):
                return

            try:
                issue.debug = str(
                    solver.get_transaction_sequence(
                        state, node.constraints + [annotation.constraint]
                    )
                )
            except UnsatError:
                return
            if annotation.operator == "subtraction":
                self.underflow_cache[address] = True
            else:
                self.overflow_cache[address] = True

            self._issues.append(issue)

    def _handle_jumpi(self, state):
        stack = state.mstate.stack
        value = stack[-2]

        for annotation in value.annotations:
            if not isinstance(annotation, OverUnderflowAnnotation):
                continue
            ostate = annotation.overflowing_state
            node = ostate.node
            issue = Issue(
                contract=node.contract_name,
                function_name=node.function_name,
                address=ostate.get_current_instruction()["address"],
                swc_id=INTEGER_OVERFLOW_AND_UNDERFLOW,
                bytecode=ostate.environment.code.bytecode,
                title="Integer Overflow",
                _type="Warning",
                gas_used=(state.mstate.min_gas_used, state.mstate.max_gas_used),
            )

            issue.description = "This binary {} operation can result in integer overflow.\n".format(
                annotation.operator
            )
            try:
                issue.debug = str(
                    solver.get_transaction_sequence(
                        state, node.constraints + [annotation.constraint]
                    )
                )
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
