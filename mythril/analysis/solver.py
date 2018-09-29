from z3 import Solver, simplify, sat, unknown
from mythril.exceptions import UnsatError
import logging


def get_model(constraints):

    constraints.solver.set("timeout", 100000)
    result = constraints.solver.check()
    if result == sat:
        return constraints.solver.model()
    elif result == unknown:
        logging.info("Timeout encountered while solving expression using z3")
    raise UnsatError


def pretty_print_model(model):

    ret = ""

    for d in model.decls():

        try:
            condition = "0x%x" % model[d].as_long()
        except:
            condition = str(simplify(model[d]))

        ret += ("%s: %s\n" % (d.name(), condition))

    return ret
