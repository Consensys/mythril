import re
from mythril.analysis.swc_data import DELEGATECALL_TO_UNTRUSTED_CONTRACT
from mythril.analysis.ops import get_variable, VarType
from mythril.analysis.report import Issue
from mythril.analysis.modules.base import DetectionModule


class DelegateCallModule(DetectionModule):
    def __init__(self):
        super().__init__(
            name="DELEGATECALL Usage in Fallback Function",
            swc_id=DELEGATECALL_TO_UNTRUSTED_CONTRACT,
            hooks=["DELEGATECALL"],
            description="Check for invocations of delegatecall(msg.data) in the fallback function.",
        )

    def execute(self, statespace):
        """
        Executes analysis module for delegate call analysis module
        :param statespace: Statespace to analyse
        :return: Found issues
        """
        issues = []

        for call in statespace.calls:

            if call.type is not "DELEGATECALL":
                continue
            if call.node.function_name is not "fallback":
                continue

            state = call.state
            address = state.get_current_instruction()["address"]
            meminstart = get_variable(state.mstate.stack[-3])

            if meminstart.type == VarType.CONCRETE:
                issues += self._concrete_call(call, state, address, meminstart)

        return issues

    def _concrete_call(self, call, state, address, meminstart):
        if not re.search(r"calldata.*_0", str(state.mstate.memory[meminstart.val])):
            return []

        issue = Issue(
            contract=call.node.contract_name,
            function_name=call.node.function_name,
            address=address,
            swc_id=DELEGATECALL_TO_UNTRUSTED_CONTRACT,
            bytecode=state.environment.code.bytecode,
            title="Call data forwarded with delegatecall()",
            _type="Informational",
            gas_used=(state.mstate.min_gas_used, state.mstate.max_gas_used),
        )

        issue.description = (
            "This contract forwards its call data via DELEGATECALL in its fallback function. "
            "This means that any function in the called contract can be executed. Note that the callee contract will have "
            "access to the storage of the calling contract.\n"
        )

        target = hex(call.to.val) if call.to.type == VarType.CONCRETE else str(call.to)
        issue.description += "DELEGATECALL target: {}".format(target)

        return [issue]


detector = DelegateCallModule()
