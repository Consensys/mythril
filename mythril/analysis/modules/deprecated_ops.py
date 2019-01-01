from mythril.analysis.report import Issue
from mythril.analysis.swc_data import DEPRICATED_FUNCTIONS_USAGE
from mythril.analysis.modules.base import DetectionModule
from mythril.laser.ethereum.state.global_state import GlobalState
import logging

log = logging.getLogger(__name__)

DESCRIPTION = """
Check for usage of deprecated opcodes
"""


def _analyze_state(state):
    node = state.node
    instruction = state.get_current_instruction()

    if instruction["opcode"] == "ORIGIN":
        log.debug("ORIGIN in function " + node.function_name)
        title = "Use of tx.origin"
        description_head = "Use of tx.origin is deprecated."
        description_tail = (
            "The smart contract retrieves the transaction origin (tx.origin) using msg.origin. "
            "Use of msg.origin is deprecated and the instruction may be removed in the  future. "
            "Use msg.sender instead.\nSee also: "
            "https://solidity.readthedocs.io/en/develop/security-considerations.html#tx-origin".format(
                node.function_name
            )
        )
        swc_id = DEPRICATED_FUNCTIONS_USAGE

    elif instruction["opcode"] == "CALLCODE":
        log.debug("CALLCODE in function " + node.function_name)
        title = "Use of callcode"
        description_head = "Use of callcode is deprecated."
        description_tail = (
            "The callcode method executes code of another contract in the context of the caller account. "
            "Due to a bug in the implementation it does not persist sender and value over the call. It was "
            "therefore deprecated and may be removed in the future. Use the delegatecall method instead."
        )
        swc_id = DEPRICATED_FUNCTIONS_USAGE

    issue = Issue(
        contract=node.contract_name,
        function_name=node.function_name,
        address=instruction["address"],
        title=title,
        bytecode=state.environment.code.bytecode,
        swc_id=swc_id,
        severity="Medium",
        description_head=description_head,
        description_tail=description_tail,
        gas_used=(state.mstate.min_gas_used, state.mstate.max_gas_used),
    )
    return [issue]


class DeprecatedOperationsModule(DetectionModule):
    def __init__(self):
        super().__init__(
            name="Deprecated Operations",
            swc_id=DEPRICATED_FUNCTIONS_USAGE,
            description=(DESCRIPTION),
            entrypoint="callback",
            pre_hooks=["ORIGIN", "CALLCODE"],
        )
        self._issues = []

    def execute(self, state: GlobalState):
        self._issues.extend(_analyze_state(state))
        return self.issues

    @property
    def issues(self):
        return self._issues


detector = DeprecatedOperationsModule()
