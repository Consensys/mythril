from mythril.analysis.report import Issue
from mythril.analysis.swc_data import ASSERT_VIOLATION
from mythril.exceptions import UnsatError
from mythril.analysis import solver
from mythril.analysis.modules.base import DetectionModule
import logging


log = logging.getLogger(__name__)

class ReachableExceptionsModule(DetectionModule):
    def __init__(self):
        super().__init__(
            name="Reachable Exceptions",
            swc_id=ASSERT_VIOLATION,
            hooks=["ASSERT_FAIL"],
            description="Checks whether any exception states are reachable.",
        )

    def execute(self, statespace):

        log.debug("Executing module: EXCEPTIONS")

        issues = []

        for k in statespace.nodes:
            node = statespace.nodes[k]

            for state in node.states:

                instruction = state.get_current_instruction()
                if instruction["opcode"] == "ASSERT_FAIL":
                    try:
                        model = solver.get_model(node.constraints)
                        address = state.get_current_instruction()["address"]

                        description = (
                            "A reachable exception (opcode 0xfe) has been detected. "
                            "This can be caused by type errors, division by zero, "
                            "out-of-bounds array access, or assert violations. "
                        )
                        description += (
                            "Note that explicit `assert()` should only be used to check invariants. "
                            "Use `require()` for regular input checking."
                        )

                        debug = str(
                            solver.get_transaction_sequence(state, node.constraints)
                        )

                        issues.append(
                            Issue(
                                contract=node.contract_name,
                                function_name=node.function_name,
                                address=address,
                                swc_id=ASSERT_VIOLATION,
                                title="Exception state",
                                _type="Informational",
                                description=description,
                                bytecode=state.environment.code.bytecode,
                                debug=debug,
                                gas_used=(
                                    state.mstate.min_gas_used,
                                    state.mstate.max_gas_used,
                                ),
                            )
                        )

                    except UnsatError:
                        log.debug("[EXCEPTIONS] no model found")

        return issues


detector = ReachableExceptionsModule()
