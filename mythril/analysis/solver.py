from z3 import Solver, simplify, sat, ExprRef, SolverFor
from mythril.exceptions import UnsatError



def get_model(constraints):
    context = constraints[0].ctx
    s = Solver(ctx=context)
    s.set("timeout", 5000)
    s.add(constraints)

    if (s.check() == sat):

        return s.model()

    else:
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
