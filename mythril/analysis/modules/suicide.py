from mythril.analysis import solver
from mythril.analysis.report import Issue
from mythril.analysis.swc_data import UNPROTECTED_SELFDESTRUCT
from mythril.exceptions import UnsatError
from mythril.analysis.modules.base import DetectionModule
from mythril.laser.ethereum.state.global_state import GlobalState
import logging
import json

log = logging.getLogger(__name__)

DESCRIPTION = """
Check if the contact can be 'accidentally' killed by anyone.
For kill-able contracts, also check whether it is possible to direct the contract balance to the attacker.
"""


class SuicideModule(DetectionModule):
    """This module checks if the contact can be 'accidentally' killed by
    anyone."""

    def __init__(self):
        super().__init__(
            name="Unprotected Selfdestruct",
            swc_id=UNPROTECTED_SELFDESTRUCT,
            description=DESCRIPTION,
            entrypoint="callback",
            pre_hooks=["SUICIDE"],
        )
        self._cache_address = {}

    def reset_module(self):
        """
        Resets the module
        :return:
        """
        super().reset_module()
        self._cache_address = {}

    def execute(self, state: GlobalState):
        """

        :param state:
        :return:
        """
        self._issues.extend(self._analyze_state(state))
        return self.issues

    def _analyze_state(self, state):
        log.info("Suicide module: Analyzing suicide instruction")
        node = state.node
        instruction = state.get_current_instruction()
        if self._cache_address.get(instruction["address"], False):
            return []
        to = state.mstate.stack[-1]

        log.debug("[SUICIDE] SUICIDE in function " + node.function_name)

        description_head = "The contract can be killed by anyone."

        try:
            try:
                transaction_sequence = solver.get_transaction_sequence(
                    state,
                    node.constraints
                    + [to == 0xDEADBEEFDEADBEEFDEADBEEFDEADBEEFDEADBEEF],
                )
                description_tail = "Arbitrary senders can kill this contract and withdraw its balance to their own account."
            except UnsatError:
                transaction_sequence = solver.get_transaction_sequence(
                    state, node.constraints
                )
                description_tail = (
                    "Arbitrary senders can kill this contract but it is not possible to set the target address to which"
                    "the contract balance is sent."
                )

            debug = json.dumps(transaction_sequence, indent=4)
            self._cache_address[instruction["address"]] = True

            issue = Issue(
                contract=node.contract_name,
                function_name=node.function_name,
                address=instruction["address"],
                swc_id=UNPROTECTED_SELFDESTRUCT,
                bytecode=state.environment.code.bytecode,
                title="Unprotected Selfdestruct",
                severity="High",
                description_head=description_head,
                description_tail=description_tail,
                debug=debug,
                gas_used=(state.mstate.min_gas_used, state.mstate.max_gas_used),
            )
            return [issue]
        except UnsatError:
            log.info("[UNCHECKED_SUICIDE] no model found")

        return []


detector = SuicideModule()
