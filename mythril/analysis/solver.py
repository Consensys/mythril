from z3 import simplify, sat, unknown, FuncInterp, Extract, UGE, Optimize
from mythril.exceptions import UnsatError
from mythril.laser.ethereum.transaction.transaction_models import (
    ContractCreationTransaction,
)
import logging


def get_model(constraints, maximize=(), minimize=()):
    s = Optimize()
    s.set("timeout", 100000)

    for constraint in constraints:
        s.add(constraint)
    for objective in maximize:
        s.maximize(objective)
    for objective in minimize:
        s.minimize(objective)

    result = s.check()
    if result == sat:
        return s.model()
    elif result == unknown:
        logging.info("Timeout encountered while solving expression using z3")
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


def get_transaction_sequence(
    global_state,
    constraints,
    caller="0xCA11EDEADBEEFCA11EDEADBEEFCA11ED37E636E6",
    max_callvalue=None,
):
    """
    Generate concrete transaction sequence

    :param global_state: GlobalState to generate transaction sequence for
    :param constraints: list of constraints used to generate transaction sequence
    :param caller: address of caller
    :param max_callvalue: maximum callvalue for a transaction
    """

    transaction_sequence = global_state.world_state.transaction_sequence

    # gaslimit & gasprice don't exist yet
    tx_template = {"calldata": None, "call_value": None, "caller": caller}

    txs = {}
    creation_tx_ids = []
    tx_constraints = constraints.copy()
    minimize = []

    for transaction in transaction_sequence:
        tx_id = str(transaction.id)
        if not isinstance(transaction, ContractCreationTransaction):

            # Constrain caller
            tx_constraints.append(
                (Extract(159, 0, transaction.caller) == int(caller[2:], 16))
            )

            # Constrain callvalue
            if max_callvalue != None:
                tx_constraints.append(UGE(max_callvalue, transaction.call_value))

            # Constrain calldatasize
            max_calldatasize = 5000
            if max_calldatasize != None:
                tx_constraints.append(
                    UGE(max_calldatasize, transaction.call_data.calldatasize)
                )

            minimize.append(transaction.call_data.calldatasize)
            txs[tx_id] = tx_template.copy()

        else:
            creation_tx_ids.append(tx_id)

    model = get_model(tx_constraints, minimize=minimize)

    for transaction in transaction_sequence:
        if not isinstance(transaction, ContractCreationTransaction):
            tx_id = str(transaction.id)

            txs[tx_id]["calldata"] = "0x" + "".join(
                [
                    hex(b)[2:] if len(hex(b)) % 2 == 0 else "0" + hex(b)[2:]
                    for b in transaction.call_data.concretized(model)
                ]
            )

    for d in model.decls():
        name = d.name()

        if "call_value" in name:
            tx_id = name.replace("call_value", "")
            if not tx_id in creation_tx_ids:
                call_value = "0x%x" % model[d].as_long()

                txs[tx_id]["call_value"] = call_value

    return txs
