from mythril.analysis.report import Issue
from mythril.analysis.module.base import DetectionModule


class Function(DetectionModule):
    name = "Show functions visited"
    swc_id = "0"
    description = "Show functions visited"
    pre_hooks = ["RETURN", "STOP"]

    def _execute(self, state):

        issue = Issue(
            contract=state.environment.active_account.contract_name,
            function_name=state.environment.active_function_name,
            bytecode=state.environment.code.bytecode,
            title="function visited",
            address=0,
            swc_id=Function.swc_id,
            severity="Low",
            description_head="function visited",
            description_tail="",
            gas_used=(state.mstate.min_gas_used, state.mstate.max_gas_used),
        )
        return [issue]


detector = Function()
