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
        description = (
            "The function `{}` retrieves the transaction origin (tx.origin) using the ORIGIN opcode. "
            "Use msg.sender instead.\nSee also: "
            "https://solidity.readthedocs.io/en/develop/security-considerations.html#tx-origin".format(
                node.function_name
            )
        )
        swc_id = DEPRICATED_FUNCTIONS_USAGE

    elif instruction["opcode"] == "CALLCODE":
        log.debug("CALLCODE in function " + node.function_name)
        title = "Use of callcode"
        description = (
            "The function `{}` uses callcode. Callcode does not persist sender or value over the call. "
            "Use delegatecall instead.".format(node.function_name)
        )
        swc_id = DEPRICATED_FUNCTIONS_USAGE

    issue = Issue(
        contract=node.contract_name,
        function_name=node.function_name,
        address=instruction["address"],
        title=title,
        bytecode=state.environment.code.bytecode,
        _type="Warning",
        swc_id=swc_id,
        description=description,
        gas_used=(state.mstate.min_gas_used, state.mstate.max_gas_used),
    )
    return [issue]


class DeprecatedOperationsModule(DetectionModule):
    def __init__(self):
        super().__init__(
            name="Deprecated Operations",
            swc_id=DEPRICATED_FUNCTIONS_USAGE,
            hooks=["ORIGIN", "CALLCODE"],
            description=(DESCRIPTION),
            entrypoint="callback",
        )
        self._issues = []

    def execute(self, state: GlobalState):
        self._issues.extend(_analyze_state(state))
        return self.issues

    @property
    def issues(self):
        return self._issues


detector = DeprecatedOperationsModule()
