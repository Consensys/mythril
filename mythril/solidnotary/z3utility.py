from z3 import Solver, sat, simplify, is_bool, is_true, is_false
from copy import deepcopy

def are_satisfiable(constraints):
    s = Solver()
    for c in constraints:
        s.add(c)
    return s.check() == sat

def simplify_constraints(constraints): # Todo simplification of the sum of constraints
    simp_const = []
    for const in constraints:
        simp_const.append(simplify(const))
    simp_const = list(filter(lambda c: not is_bool(c) or not is_true(c), simp_const))
    falses = list(filter(lambda c: is_bool(c) and is_false(c), simp_const))
    if len(falses) > 0:
        return [deepcopy(falses[0])]

    return simp_const
