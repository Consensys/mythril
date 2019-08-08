"""This module contains analysis module helpers to solve path constraints."""
from functools import lru_cache
from typing import Dict, Tuple, Union
from z3 import sat, unknown, FuncInterp
import z3

from mythril.analysis.analysis_args import analysis_args
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

# LRU cache works great when used in powers of 2
@lru_cache(maxsize=2 ** 23)
def get_model(constraints, minimize=(), maximize=(), enforce_execution_time=True):
    """

    :param constraints:
    :param minimize:
    :param maximize:
    :param enforce_execution_time: Bool variable which enforces --execution-timeout's time
    :return:
    """
    s = Optimize()
    timeout = analysis_args.solver_timeout
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
    """ Pretty prints a z3 model

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

    tx_constraints, minimize = _set_minimisation_constraints(
        transaction_sequence, constraints.copy(), [], 5000
    )

    try:
        model = get_model(tx_constraints, minimize=minimize)
    except UnsatError:
        raise UnsatError

    min_price_dict = {}  # type: Dict[str, int]
    for transaction in transaction_sequence:
        concrete_transaction = _get_concrete_transaction(model, transaction)
        concrete_transactions.append(concrete_transaction)

        caller = concrete_transaction["origin"]
        value = int(concrete_transaction["value"], 16)
        min_price_dict[caller] = min_price_dict.get(caller, 0) + value

    if isinstance(transaction_sequence[0], ContractCreationTransaction):
        initial_accounts = transaction_sequence[0].prev_world_state.accounts
    else:
        initial_accounts = transaction_sequence[0].world_state.accounts

    concrete_initial_state = _get_concrete_state(initial_accounts, min_price_dict)

    steps = {"initialState": concrete_initial_state, "steps": concrete_transactions}

    return steps


def _get_concrete_state(initial_accounts: Dict, min_price_dict: Dict[str, int]):
    """ Gets a concrete state """
    accounts = {}
    for address, account in initial_accounts.items():
        # Skip empty default account

        data = dict()  # type: Dict[str, Union[int, str]]
        data["nonce"] = account.nonce
        data["code"] = account.code.bytecode
        data["storage"] = str(account.storage)
        data["balance"] = hex(min_price_dict.get(address, 0))
        accounts[hex(address)] = data
    return {"accounts": accounts}


def _get_concrete_transaction(model: z3.Model, transaction: BaseTransaction):
    """ Gets a concrete transaction from a transaction and z3 model"""
    # Get concrete values from transaction
    address = hex(transaction.callee_account.address.value)
    value = model.eval(transaction.call_value.raw, model_completion=True).as_long()
    caller = "0x" + (
        "%x" % model.eval(transaction.caller.raw, model_completion=True).as_long()
    ).zfill(40)

    if isinstance(transaction, ContractCreationTransaction):
        address = ""
        input_ = transaction.code.bytecode
    else:
        input_ = "".join(
            [
                hex(b)[2:] if len(hex(b)) % 2 == 0 else "0" + hex(b)[2:]
                for b in transaction.call_data.concrete(model)
            ]
        )

    # Create concrete transaction dict
    concrete_transaction = dict()  # type: Dict[str, str]
    concrete_transaction["input"] = "0x" + input_
    concrete_transaction["value"] = "0x%x" % value
    # Fixme: base origin assignment on origin symbol
    concrete_transaction["origin"] = caller
    concrete_transaction["address"] = "%s" % address

    return concrete_transaction


def _set_minimisation_constraints(
    transaction_sequence, constraints, minimize, max_size
) -> Tuple[Constraints, tuple]:
    """ Set constraints that minimise key transaction values

    Constraints generated:
    - Upper bound on calldata size
    - Minimisation of call value's and calldata sizes

    :param transaction_sequence: Transaction for which the constraints should be applied
    :param constraints: The constraints array which should contain any added constraints
    :param minimize: The minimisation array which should contain any variables that should be minimised
    :param max_size: The max size of the calldata array
    :return: updated constraints, minimize
    """
    for transaction in transaction_sequence:
        # Set upper bound on calldata size
        max_calldata_size = symbol_factory.BitVecVal(max_size, 256)
        constraints.append(UGE(max_calldata_size, transaction.call_data.calldatasize))

        # Minimize
        minimize.append(transaction.call_data.calldatasize)
        minimize.append(transaction.call_value)

    return constraints, tuple(minimize)
