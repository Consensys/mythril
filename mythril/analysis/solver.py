from z3 import Solver, simplify, sat, unknown, FuncInterp, Extract
from mythril.exceptions import UnsatError
from mythril.laser.ethereum.transaction.transaction_models import (
    ContractCreationTransaction,
)
import logging


def get_model(constraints):
    s = Solver()
    s.set("timeout", 100000)

    for constraint in constraints:
        s.add(constraint)
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
    tx_template = {"calldata": [], "call_value": None, "caller": caller}

    txs = {}
    creation_tx_ids = []
    tx_constraints = constraints.copy()

    for transaction in transaction_sequence:
        if not isinstance(transaction, ContractCreationTransaction):
            # Constrain caller
            tx_constraints.append(
                (Extract(159, 0, transaction.caller) == int(caller[2:], 16))
            )

            # Constrain callvalue
            if max_callvalue != None:
                tx_constraints.append(UGE(max_callvalue, transaction.call_value))

            txs[str(transaction.id)] = tx_template
        else:
            creation_tx_ids.append(str(transaction.id))

    model = get_model(tx_constraints)

    for d in model.decls():
        name = d.name()

        logging.debug(name)
        if "call_value" in name:
            tx_id = name.replace("call_value", "")
            if not tx_id in creation_tx_ids:
                call_value = "0x%x" % model[d].as_long()

                txs[tx_id]["call_value"] = call_value

    # Copy calldata
    for tx_id in txs:
        txs[tx_id]["calldata"] = "0x" + "".join(
            [str(x) for x in global_state.environment.calldata.concretized(model)]
        )

    return txs
