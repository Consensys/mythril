from mythril.analysis import solver
from mythril.analysis.report import Issue
from mythril.analysis.swc_data import WRITE_TO_ARBITRARY_STORAGE
from mythril.exceptions import UnsatError
from mythril.analysis.modules.base import DetectionModule
from mythril.laser.ethereum.state.global_state import GlobalState
import logging
import json

log = logging.getLogger(__name__)

DESCRIPTION = """
Check if an arbitrary storage location can be written to by anyone.
"""


class ArbitraryWriteModule(DetectionModule):
    """This module checks if an arbitrary storage location in the contact can be written to by anyone."""

    def __init__(self):
        super().__init__(
            name="Write to Arbitrary Storage",
            swc_id=WRITE_TO_ARBITRARY_STORAGE,
            description=DESCRIPTION,
            entrypoint="callback",
            pre_hooks=["SSTORE"],
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
        """
        Analyzes a global state

        :param state:
        :return: List of found issues
        """
        log.debug("Analyzing SSTORE instruction")
        node = state.node
        instruction = state.get_current_instruction()
        if self._cache_address.get(instruction["address"], False):
            return []

        dest = state.mstate.stack[-1]

        description_head = "Arbitrary senders can write to any location in storage."
        try:
            transaction_sequence = solver.get_transaction_sequence(
                state,
                node.constraints + [dest == 0xDEADBEEFDEADBEEFDEADBEEFDEADBEEF123],
            )
            description_tail = "Anyone can modify any storage variable. This is likely to be a high severity vulnerability, as authentication checks can be easily circumvented by, for example, overwriting the contract owner."

            debug = json.dumps(transaction_sequence, indent=4)
            self._cache_address[instruction["address"]] = True

            issue = Issue(
                contract=node.contract_name,
                function_name=node.function_name,
                address=instruction["address"],
                swc_id=WRITE_TO_ARBITRARY_STORAGE,
                bytecode=state.environment.code.bytecode,
                title="Write to Arbitrary Storage",
                severity="High",
                description_head=description_head,
                description_tail=description_tail,
                debug=debug,
                gas_used=(state.mstate.min_gas_used, state.mstate.max_gas_used),
            )
            return [issue]
        except UnsatError:
            log.debug("No model found")

        return []


detector = ArbitraryWriteModule()
