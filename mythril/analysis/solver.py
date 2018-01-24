from z3 import *
from mythril.exceptions import UnsatError
import logging

def get_model(constraints):
    s = Solver()
    s.set("timeout", 2000)

    for constraint in constraints:
        s.add(constraint)

    if (s.check() == sat):

        return s.model()

    else:
        raise UnsatError