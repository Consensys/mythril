from z3 import Solver, simplify, sat, unknown, FuncInterp, UGE, Optimize
from mythril.exceptions import UnsatError
from mythril.laser.ethereum.transaction.transaction_models import (
    ContractCreationTransaction,
)
import logging


def get_model(constraints, minimize=(), maximize=()):
    s = Optimize()
    s.set("timeout", 100000)

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
        logging.debug("Timeout encountered while solving expression using z3")
    raise UnsatError


def pretty_print_model(model):

    ret = ""

    for d in model.decls():
        if type(model[d]) == FuncInterp:
            condition = model[d].as_list()
            ret += "%s: %s\n" % (d.name(), condition)
            continue

        try:
            condition = "0x%x" % model[d].as_long()
        except:
            condition = str(simplify(model[d]))

        ret += "%s: %s\n" % (d.name(), condition)

    return ret


def get_transaction_sequence(global_state, constraints):
    """
    Generate concrete transaction sequence

    :param global_state: GlobalState to generate transaction sequence for
    :param constraints: list of constraints used to generate transaction sequence
    :param caller: address of caller
    :param max_callvalue: maximum callvalue for a transaction
    """

    transaction_sequence = global_state.world_state.transaction_sequence

    # gaslimit & gasprice don't exist yet
    tx_template = {
        "calldata": None,
        "call_value": None,
        "caller": "0xCA11EDEADBEEF37E636E6CA11EDEADBEEFCA11ED",
    }

    concrete_transactions = {}
    creation_tx_ids = []
    tx_constraints = constraints.copy()
    minimize = []

    transactions = []

    for transaction in transaction_sequence:
        tx_id = str(transaction.id)
        if not isinstance(transaction, ContractCreationTransaction):
            transactions.append(transaction)
            # Constrain calldatasize
            max_calldatasize = 5000
            if max_calldatasize != None:
                tx_constraints.append(
                    UGE(max_calldatasize, transaction.call_data.calldatasize)
                )

            minimize.append(transaction.call_data.calldatasize)

            concrete_transactions[tx_id] = tx_template.copy()

        else:
            creation_tx_ids.append(tx_id)

    model = get_model(tx_constraints, minimize=minimize)

    for transaction in transactions:
        tx_id = str(transaction.id)

        concrete_transactions[tx_id]["calldata"] = "0x" + "".join(
            [
                hex(b)[2:] if len(hex(b)) % 2 == 0 else "0" + hex(b)[2:]
                for b in transaction.call_data.concrete(model)
            ]
        )

        concrete_transactions[tx_id]["call_value"] = (
            "0x%x" % model.eval(transaction.call_value, model_completion=True).as_long()
        )
        concrete_transactions[tx_id]["caller"] = "0x" + (
            "%x" % model.eval(transaction.caller, model_completion=True).as_long()
        ).zfill(40)

    return concrete_transactions
