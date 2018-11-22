from mythril.analysis import solver
from mythril.analysis.analysis_utils import get_non_creator_constraints
from mythril.analysis.ops import *
from mythril.analysis.report import Issue
from mythril.analysis.swc_data import UNPROTECTED_SELFDESTRUCT
from mythril.exceptions import UnsatError
from mythril.analysis.modules.base import DetectionModule
from mythril.laser.ethereum.state.global_state import GlobalState
import logging


def _analyze_state(state):
    logging.info("Suicide module: Analyzing suicide instruction")
    node = state.node
    instruction = state.get_current_instruction()
    to = state.mstate.stack[-1]

    logging.debug("[UNCHECKED_SUICIDE] suicide in function " + node.function_name)

    description = "A reachable SUICIDE instruction was detected. "

    if "caller" in str(to):
        description += "The remaining Ether is sent to the caller's address.\n"
    elif "storage" in str(to):
        description += "The remaining Ether is sent to a stored address.\n"
    elif "calldata" in str(to):
        description += "The remaining Ether is sent to an address provided as a function argument.\n"
    elif type(to) == BitVecNumRef:
        description += "The remaining Ether is sent to: " + hex(to.as_long()) + "\n"
    else:
        description += "The remaining Ether is sent to: " + str(to) + "\n"

    not_creator_constraints, constrained = get_non_creator_constraints(state)

    if constrained:
        return []
    try:
        solver.get_model(node.constraints + not_creator_constraints)

        debug = "Transaction Sequence: " + str(
            solver.get_transaction_sequence(
                state, node.constraints + not_creator_constraints
            )
        )

        issue = Issue(
            contract=node.contract_name,
            function_name=node.function_name,
            address=instruction["address"],
            swc_id=UNPROTECTED_SELFDESTRUCT,
            bytecode=state.environment.code.bytecode,
            title="Unchecked SUICIDE",
            _type="Warning",
            description=description,
            debug=debug,
            gas_used=(state.mstate.min_gas_used, state.mstate.max_gas_used),
        )
        return [issue]
    except UnsatError:
        logging.info("[UNCHECKED_SUICIDE] no model found")

    return []


class Singleton(type):
    _instances = {}

    def __call__(cls, *args, **kwargs):
        if cls not in cls._instances:
            cls._instances[cls] = super(Singleton, cls).__call__(*args, **kwargs)
        return cls._instances[cls]


class SuicideModule(DetectionModule, metaclass=Singleton):
    def __init__(self):
        super().__init__(
            name="Unprotected Suicide",
            swc_id=UNPROTECTED_SELFDESTRUCT,
            hooks=["SUICIDE"],
            description=(
                "Check for SUICIDE instructions that either can be reached by anyone, "
                "or where msg.sender is checked against a tainted storage index (i.e. "
                "there's a write to that index is unconstrained by msg.sender)."
            ),
            entrypoint="callback"
        )
        self._issues = []

    def execute(self, state: GlobalState):
        self._issues.extend(_analyze_state(state))
        return self.issues

    @property
    def issues(self):
        return self._issues


detector = SuicideModule()
