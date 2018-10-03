from z3 import Solver, simplify, sat, unknown
from mythril.exceptions import UnsatError
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

        try:
            condition = "0x%x" % model[d].as_long()
        except:
            condition = str(simplify(model[d]))

        ret += ("%s: %s\n" % (d.name(), condition))

    return ret
