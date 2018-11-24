from mythril.analysis import solver
from mythril.analysis.analysis_utils import get_non_creator_constraints
from mythril.analysis.report import Issue
from mythril.analysis.swc_data import UNPROTECTED_SELFDESTRUCT
from mythril.exceptions import UnsatError
from mythril.analysis.modules.base import DetectionModule
import logging


DESCRIPTION = """

Check if the contact can be 'accidentally' killed by anyone.
For killable contracts, also check whether it is possible to direct the contract balance to the attacker.
s
"""

ARBITRARY_SENDER_ADDRESS = 0xAAAAAAAABBBBBBBBBCCCCCCCDDDDDDDDEEEEEEEE


class SuicideModule(DetectionModule):
    def __init__(self):
        super().__init__(
            name="Unprotected Suicide",
            swc_id=UNPROTECTED_SELFDESTRUCT,
            hooks=["SUICIDE"],
            description=DESCRIPTION,
        )

    def execute(self, state_space):

        logging.debug("Executing module: SUICIDE")

        issues = []

        for k in state_space.nodes:
            node = state_space.nodes[k]

            for state in node.states:
                issues += self._analyze_state(state, node)

        return issues

    def _analyze_state(self, state, node):
        issues = []
        instruction = state.get_current_instruction()

        if instruction["opcode"] != "SUICIDE":
            return []

        to = state.mstate.stack[-1]

        logging.debug("[SUICIDE] SUICIDE in function " + node.function_name)

        not_creator_constraints, constrained = get_non_creator_constraints(state)
        constraints = (
            node.constraints
            + not_creator_constraints
            + [state.environment.sender == ARBITRARY_SENDER_ADDRESS]
        )

        if constrained:
            return []

        try:
            try:
                transaction_sequence = solver.get_transaction_sequence(
                    state, constraints + [to == ARBITRARY_SENDER_ADDRESS]
                )
                description = "Anyone can kill this contract and withdraw its balance to their own account."
            except UnsatError:
                transaction_sequence = solver.get_transaction_sequence(
                    state, constraints
                )
                description = (
                    "The contract can be killed by anyone. Don't accidentally kill it."
                )

            debug = "Transaction Sequence: " + str(transaction_sequence)

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
            issues.append(issue)
        except UnsatError:
            logging.debug("[SUICIDE] no model found")

        return issues


detector = SuicideModule()
