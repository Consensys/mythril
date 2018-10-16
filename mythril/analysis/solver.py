from mythril.exceptions import UnsatError
from mythril.laser.ethereum.smt_wrapper import \
    NotConcreteValueError, get_concrete_value, \
    simplify, solve, Result, Solver
import logging

def get_model(constraints):
    s = Solver(timeout=100000)

    for constraint in constraints:
        s.add_assertion(constraint)
    result = solve(s)
    if result == Result.sat:
        return s.get_model()
    elif result == Result.unknown:
        logging.info("Timeout encountered while solving expression using z3")
    raise UnsatError


def pretty_print_model(model):

    ret = ""

    for (name, value) in model:

        try:
            condition = "0x%x" % get_concrete_value(value)
        except NotConcreteValueError:
            condition = str(simplify(value))

        ret += ("%s: %s\n" % (name, condition))

    return ret
