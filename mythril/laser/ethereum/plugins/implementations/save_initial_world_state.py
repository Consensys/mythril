from mythril.laser.ethereum.svm import LaserEVM
from mythril.laser.ethereum.plugins.plugin import LaserPlugin
from mythril.laser.ethereum.state.world_state import WorldState

from typing import List

import logging

log = logging.getLogger(__name__)


class SaveInitialWorldState(LaserPlugin):
    """SaveInitialWorldState
    This plugin is used to save initial world state so it can be used for the output to display

    """

    def __init__(self):
        pass

    def initialize(self, symbolic_vm: LaserEVM):
        """
        :param symbolic_vm:
        :return:
        """

        @symbolic_vm.laser_hook("end_contract_creation")
        def set_standard_initial_state(openstates: List[WorldState]):
            """
            This function initializes the initial state to all the open states
            :param openstates:
            :return:
            """
            accounts = openstates[0].accounts
            initial_state = openstates[0].initial_state_account
            initial_state[
                "accounts"
            ] = {}  # This variable persists for all world states.
            for address, account in accounts.items():
                if address == "0x" + "0" * 40:
                    continue
                initial_state["accounts"][address] = {
                    "nounce": account.nonce,
                    "balance": "<ARBITRARY_BALANCE>",
                    "code": account.code.bytecode,
                    "storage": {},
                }
