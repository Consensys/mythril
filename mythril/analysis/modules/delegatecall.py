import re
import logging
from typing import List

from mythril.analysis.swc_data import DELEGATECALL_TO_UNTRUSTED_CONTRACT
from mythril.analysis.ops import get_variable, VarType, Call, Variable
from mythril.analysis.report import Issue
from mythril.analysis.call_helpers import get_call_from_state
from mythril.analysis.modules.base import DetectionModule
from mythril.laser.ethereum.state.global_state import GlobalState


log = logging.getLogger(__name__)


class DelegateCallModule(DetectionModule):
    def __init__(self):
        super().__init__(
            name="DELEGATECALL Usage in Fallback Function",
            swc_id=DELEGATECALL_TO_UNTRUSTED_CONTRACT,
            description="Check for invocations of delegatecall(msg.data) in the fallback function.",
            entrypoint="callback",
            pre_hooks=["DELEGATECALL"],
        )
        self._issues = []

    @property
    def issues(self) -> list:
        return self._issues

    def execute(self, state: GlobalState) -> list:
        log.debug("Executing module: DELEGATE_CALL")
        self._issues.extend(_analyze_states(state))
        return self.issues


def _analyze_states(state: GlobalState) -> List[Issue]:
    """
    :param state: the current state
    :return: returns the issues for that corresponding state
    """
    call = get_call_from_state(state)
    if call is None:
        return []
    issues = []

    if call.type is not "DELEGATECALL":
        return []
    if call.node.function_name is not "fallback":
        return []

    state = call.state
    address = state.get_current_instruction()["address"]
    meminstart = get_variable(state.mstate.stack[-3])

    if meminstart.type == VarType.CONCRETE:
        issues += _concrete_call(call, state, address, meminstart)

    return issues


def _concrete_call(
    call: Call, state: GlobalState, address: int, meminstart: Variable
) -> List[Issue]:
    """
    :param call: The current call's information
    :param state: The current state
    :param address: The PC address
    :param meminstart: memory starting position
    :return: issues
    """
    if not re.search(r"calldata.*\[0", str(state.mstate.memory[meminstart.val])):
        return []

    issue = Issue(
        contract=call.node.contract_name,
        function_name=call.node.function_name,
        address=address,
        swc_id=DELEGATECALL_TO_UNTRUSTED_CONTRACT,
        bytecode=state.environment.code.bytecode,
        title="Delegatecall Proxy",
        severity="Low",
        description_head="The contract implements a delegatecall proxy.",
        description_tail="The smart contract forwards the received calldata via delegatecall. Note that callers"
                         "can execute arbitrary functions in the callee contract and that the callee contract "
                         "can access the storage of the calling contract. " 
                         "Make sure that the callee contract is audited properly.",
        gas_used=(state.mstate.min_gas_used, state.mstate.max_gas_used),
    )

    issue.description = (
        ""
        "This means that any function in the called contract can be executed. Note that the callee contract will have "
        "access to the storage of the calling contract.\n"
    )

    target = hex(call.to.val) if call.to.type == VarType.CONCRETE else str(call.to)
    issue.description += "DELEGATECALL target: {}".format(target)

    return [issue]


detector = DelegateCallModule()
