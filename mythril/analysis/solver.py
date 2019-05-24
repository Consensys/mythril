"""This module contains analysis module helpers to solve path constraints."""
from typing import Dict, List, Union
from z3 import sat, unknown, FuncInterp
import z3

from mythril.laser.ethereum.state.global_state import GlobalState
from mythril.laser.ethereum.state.constraints import Constraints
from mythril.laser.ethereum.transaction import BaseTransaction
from mythril.laser.smt import UGE, Optimize, symbol_factory
from mythril.laser.ethereum.time_handler import time_handler
from mythril.exceptions import UnsatError
from mythril.laser.ethereum.transaction.transaction_models import (
    ContractCreationTransaction,
)
import logging

log = logging.getLogger(__name__)


def get_model(constraints, minimize=(), maximize=(), enforce_execution_time=True):
    """

    :param constraints:
    :param minimize:
    :param maximize:
    :param enforce_execution_time: Bool variable which enforces --execution-timeout's time
    :return:
    """
    s = Optimize()
    timeout = 100000
    if enforce_execution_time:
        timeout = min(timeout, time_handler.time_remaining() - 500)
        if timeout <= 0:
            raise UnsatError
    s.set_timeout(timeout)
    for constraint in constraints:
        if type(constraint) == bool and not constraint:
            raise UnsatError

    constraints = [constraint for constraint in constraints if type(constraint) != bool]

    for constraint in constraints:
        s.add(constraint)
    for e in minimize:
        s.minimize(e)
    for e in maximize:
        s.maximize(e)

    result = s.check()
    if result == sat:
        return s.model()
    elif result == unknown:
        log.debug("Timeout encountered while solving expression using z3")
    raise UnsatError


def pretty_print_model(model):
    """

    :param model:
    :return:
    """
    ret = ""

    for d in model.decls():
        if type(model[d]) == FuncInterp:
            condition = model[d].as_list()
            ret += "%s: %s\n" % (d.name(), condition)
            continue

        try:
            condition = "0x%x" % model[d].as_long()
        except:
            condition = str(z3.simplify(model[d]))

        ret += "%s: %s\n" % (d.name(), condition)

    return ret


def get_transaction_sequence(
    global_state: GlobalState, constraints: Constraints
) -> Dict:
    """Generate concrete transaction sequence.

    :param global_state: GlobalState to generate transaction sequence for
    :param constraints: list of constraints used to generate transaction sequence
    """

    transaction_sequence = global_state.world_state.transaction_sequence

    concrete_transactions = []
    creation_tx_ids = []
    tx_constraints = constraints.copy()
    minimize = []

    transactions = []  # type: List[BaseTransaction]
    for transaction in transaction_sequence:
        tx_id = str(transaction.id)
        if not isinstance(transaction, ContractCreationTransaction):
            transactions.append(transaction)
            # Constrain calldatasize
            max_calldatasize = symbol_factory.BitVecVal(5000, 256)
            tx_constraints.append(
                UGE(max_calldatasize, transaction.call_data.calldatasize)
            )

            minimize.append(transaction.call_data.calldatasize)
            minimize.append(transaction.call_value)

        else:
            creation_tx_ids.append(tx_id)

    model = get_model(tx_constraints, minimize=minimize)
    min_price_dict = {}  # type: Dict[str, int]
    for transaction in transactions:
        concrete_transaction = dict()  # type: Dict[str, str]
        concrete_transaction["input"] = "0x" + "".join(
            [
                hex(b)[2:] if len(hex(b)) % 2 == 0 else "0" + hex(b)[2:]
                for b in transaction.call_data.concrete(model)
            ]
        )
        value = model.eval(transaction.call_value.raw, model_completion=True).as_long()
        concrete_transaction["value"] = "0x%x" % value
        caller = "0x" + (
            "%x" % model.eval(transaction.caller.raw, model_completion=True).as_long()
        ).zfill(40)

        concrete_transaction["origin"] = caller
        concrete_transaction["address"] = "%s" % transaction.callee_account.address
        concrete_transactions.append(concrete_transaction)
        min_price_dict[caller] = min_price_dict.get(caller, 0) + value
    if len(transactions) > 0:
        initial_state = transactions[0].world_state.accounts
    else:
        for transaction in transaction_sequence:
            if transaction.id == "1":
                initial_state = transaction.world_state.accounts
                break

    states = {}
    for address, account in initial_state.items():
        if address == "0x" + 40 * "0" and len(account.code.bytecode) > 0:
            continue
        data = dict()  # type: Dict[str, Union[int, str]]
        data["nonce"] = account.nonce
        data["code"] = account.code.bytecode
        data["storage"] = str(account.storage)
        data["balance"] = min_price_dict.get(address, 0)
        states[address] = data
    steps = {"initialState": states, "steps": concrete_transactions}

    return steps
