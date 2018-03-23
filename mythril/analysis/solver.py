from z3 import Solver, simplify, sat
from mythril.exceptions import UnsatError
import re


def get_model(constraints):
    s = Solver()
    s.set("timeout", 2000)

    for constraint in constraints:
        s.add(constraint)

    if (s.check() == sat):

        return s.model()

    else:
        raise UnsatError


def pretty_print_model(model):

    ret = ""

    for d in model.decls():

        try:
            if (re.match(r'^calldata_.*_(\d)+', d.name())):
                condition = "%064x" % model[d].as_long()
            else:
                condition = str(model[d].as_long())
        except:
            condition = str(simplify(model[d]))

        ret += ("%s: %s\n" % (d.name(), condition))

    return ret
