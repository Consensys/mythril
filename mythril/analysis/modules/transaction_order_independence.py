from z3 import *
from mythril.analysis.ops import *
from mythril.analysis import solver
from mythril.analysis.report import Issue
from mythril.exceptions import UnsatError
import re
import logging


'''
MODULE DESCRIPTION:

'''


def execute(statespace):

    logging.debug("Executing module: TOD")

    issues = []

    for call in statespace.calls:

        state = call.state
        node = call.node

        # Interesting values
        to, value = call.to, call.value
        storages = []
        if to.type == VarType.SYMBOLIC:
            storages += _dependent_on_storage(to.val)
        if value.type == VarType.SYMBOLIC:
            storages += _dependent_on_storage(value.val)
        print(storages)
    return issues


def _dependent_on_storage(expression):
    pattern = re.compile(r"storage_([a-z0-9_&^]+)")
    result = pattern.search(str(simplify(expression)))
    if result is not None:
        return [result.group()]
    return []


def _get_storage_variable(storage, state):
    index = int(re.search('[0-9]+', storage))
    try:
        return state.environment.active_account.storage[index]
    except KeyError:
        return None

def _can_change(constraints, variable):
    _constraints = copy.deepcopy(constraints)
    model = solver.get_model(_constraints)
    initial_value = int(str(model.eval(variable, model_completion=True)))



    # if type(op0) is not int:
    #     op0_value = int(str(model.eval(op0, model_completion=True)))
    #     model0 = _try_constraints(node.constraints, [constraint, op0 != op0_value])
    #
    # if type(op1) is not int:
    #     op1_value = int(str(model.eval(op1, model_completion=True)))
    #     model1 = _try_constraints(node.constraints, [constraint, op1 != op1_value])
    #
    # if model0 is None and model1 is None:
    #     return False
