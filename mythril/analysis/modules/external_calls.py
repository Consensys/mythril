from z3 import *
from mythril.analysis.ops import *
from mythril.analysis.report import Issue
from mythril.analysis import solver
from mythril.analysis.swc_data import REENTRANCY
from mythril.analysis.modules.base import DetectionModule
from mythril.exceptions import UnsatError
import logging


class ExternalCallModule(DetectionModule):
    def __init__(self, max_search_depth=64):
        super().__init__(
            name="External Calls",
            swc_id=REENTRANCY,
            hooks=["CALL"],
            description="Check for call.value()() to external addresses",
        )
        self.max_search_depth = max_search_depth
        self.calls_visited = []

    def execute(self, state_space):
        logging.debug("Executing module: %s", self.name)
        issues = []

        for k in state_space.nodes:
            node = state_space.nodes[k]
            for state in node.states:
                issues += self._analyze_state(state, node)

        return issues

    @staticmethod
    def _analyze_state(state, node):
        issues = []
        instruction = state.get_current_instruction()

        if instruction["opcode"] not in ("CALL", "CALLCODE", "DELEGATECALL", "STATICCALL"):
            return []

        gas = state.mstate.stack[-1]
        to = state.mstate.stack[-2]

        address = state.get_current_instruction()["address"]

        try:
            constraints = state.node.constraints + [gas > 2300]
            transaction_sequence = solver.get_transaction_sequence(state, constraints)

            try:
                constraints += [to == 0xDEADBEEFDEADBEEFDEADBEEFDEADBEEFDEADBEEF]
                transaction_sequence = solver.get_transaction_sequence(state, constraints)

            except UnsatError:
                debug = str(transaction_sequence)
                description = "The contract executes a function call to an external address. " \
                              "Verify that the code at this address is trusted and immutable."

                issue = Issue(
                    contract=node.contract_name,
                    function_name=state.node.function_name,
                    address=address,
                    swc_id=REENTRANCY,
                    title="External call",
                    _type="Informational",
                    bytecode=state.environment.code.bytecode,
                    description=description,
                    debug=debug,
                    gas_used=(state.mstate.min_gas_used, state.mstate.max_gas_used),
                )

                issues.append(issue)
                return issues

            debug = str(transaction_sequence)
            description = "The contract executes a function call with high gas to a user-supplied address. " \
                "Note that the callee can contain arbitrary code and may re-enter any function in this contract. " \
                "Review the business logic carefully to prevent unanticipated effects on the contract state."

            issue = Issue(
                contract=node.contract_name,
                function_name=node.function_name,
                address=address,
                swc_id=REENTRANCY,
                title="External call to user-supplied address",
                _type="Warning",
                bytecode=state.environment.code.bytecode,
                description=description,
                debug=debug,
                gas_used=(state.mstate.min_gas_used, state.mstate.max_gas_used),
            )
            issues.append(issue)
            return issues

        except UnsatError:
            logging.debug("[EXTERNAL_CALLS] no model found for setting caller address.")


detector = ExternalCallModule()
