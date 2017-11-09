from z3 import *
from mythril.exceptions import UnsatError

def get_model(constraints):
    s = Solver()

    for constraint in constraints:
        s.add(constraint)

    if (s.check() == sat):

        return s.model()

    else:
            raise UnsatError

