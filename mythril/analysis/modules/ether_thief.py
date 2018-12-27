from mythril.analysis.ops import *
from mythril.analysis import solver
from mythril.analysis.report import Issue
from mythril.analysis.swc_data import UNPROTECTED_ETHER_WITHDRAWAL
from mythril.analysis.modules.base import DetectionModule
from mythril.laser.ethereum.state.global_state import GlobalState
from mythril.exceptions import UnsatError
from mythril.laser.smt import symbol_factory, UGT, Sum, BVAddNoOverflow
import logging
from copy import copy

log = logging.getLogger(__name__)

DESCRIPTION = """

Search for cases where Ether can be withdrawn to a user-specified address. 

An issue is reported if:

- The transaction sender does not match contract creator;
- The sender address can be chosen arbitrarily;
- The receiver address is identical to the sender address;
- The sender can withdraw *more* than the total amount they sent over all transactions.

"""


def _analyze_state(state):
    instruction = state.get_current_instruction()
    node = state.node

    if instruction["opcode"] != "CALL":
        return []

    call_value = state.mstate.stack[-3]
    target = state.mstate.stack[-2]

    eth_sent_total = symbol_factory.BitVecVal(0, 256)

    constraints = copy(node.constraints)

    for tx in state.world_state.transaction_sequence:
        if tx.caller == 0xDEADBEEFDEADBEEFDEADBEEFDEADBEEFDEADBEEF:

            # There's sometimes no overflow check on balances added.
            # But we don't care about attacks that require more 2^^256 ETH to be sent.

            constraints += [BVAddNoOverflow(eth_sent_total, tx.call_value, False)]
            eth_sent_total = Sum(eth_sent_total, tx.call_value)
    constraints += [UGT(call_value, eth_sent_total), target == state.environment.sender]

    try:

        transaction_sequence = solver.get_transaction_sequence(state, constraints)

        debug = str(transaction_sequence)

        issue = Issue(
            contract=node.contract_name,
            function_name=node.function_name,
            address=instruction["address"],
            swc_id=UNPROTECTED_ETHER_WITHDRAWAL,
            title="Unprotected Ether Withdrawal",
            _type="High",
            bytecode=state.environment.code.bytecode,
            description_head="It appears that anyone can withdraw Ether from the contract account.",
            description_tail="Arbitrary senders other than the contract creator can withdraw ETH from the contract"
            + " account without previously having sent an equivalent amount of ETH to it. This is likely to be"
            + " a vulnerability.",
            debug=debug,
            gas_used=(state.mstate.min_gas_used, state.mstate.max_gas_used),
        )
    except UnsatError:
        log.debug("[ETHER_THIEF] no model found")
        return []

    return [issue]


class EtherThief(DetectionModule):
    def __init__(self):
        super().__init__(
            name="Ether Thief",
            swc_id=UNPROTECTED_ETHER_WITHDRAWAL,
            description=DESCRIPTION,
            entrypoint="callback",
            pre_hooks=["CALL"],
        )
        self._issues = []

    def execute(self, state: GlobalState):
        self._issues.extend(_analyze_state(state))
        return self.issues

    @property
    def issues(self):
        return self._issues


detector = EtherThief()
