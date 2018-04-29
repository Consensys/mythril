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
        interesting_storages = list(_get_influencing_storages(call))
        c = list(_find_changable(statespace, interesting_storages))
        node = call.node
        instruction = call.state.get_current_instruction()

        if len(c) > 0:
            issue = Issue(node.contract_name, node.function_name, instruction['address'], "Transaction order dependence",
                          "Warning")

            issue.description = "A possible transaction order independence vulnerability exists in function {}. The value or " \
                                "direction of the call statement is determined from a tainted storage location".format(
                node.function_name)
            # issue.debug = solver.pretty_print_model(model)
            issues.append(issue)


    return issues

def _get_states_with_opcode(statespace, opcode):
    for k in statespace.nodes:
        node = statespace.nodes[k]
        for state in node.states:
            if state.get_current_instruction()["opcode"] == opcode:
                yield state, node


def _dependent_on_storage(expression):
    pattern = re.compile(r"storage_([a-z0-9_&^]+)")
    result = pattern.search(str(simplify(expression)))
    if result is not None:
        return [result.group()]
    return []


def _get_storage_variable(storage, state):
    index = int(re.search('[0-9]+', storage).group())
    try:
        return state.environment.active_account.storage[index]
    except KeyError:
        return None


def _can_change(constraints, variable):
    _constraints = copy.deepcopy(constraints)
    model = solver.get_model(_constraints)
    initial_value = int(str(model.eval(variable, model_completion=True)))
    return _try_constraints(constraints, [variable != initial_value]) is not None


def _get_influencing_storages(call):
    state = call.state
    node = call.node

    # Get relevant storages
    to, value = call.to, call.value
    storages = []
    if to.type == VarType.SYMBOLIC:
        storages += _dependent_on_storage(to.val)
    if value.type == VarType.SYMBOLIC:
        storages += _dependent_on_storage(value.val)

    # See if they can change within the constraints of the node
    for storage in storages:
        variable = _get_storage_variable(storage, state)
        can_change = _can_change(node.constraints, variable)
        if can_change:
            yield storage


def _find_changable(statespace, interesting_storages):
    for sstore_state, node in _get_states_with_opcode(statespace, 'SSTORE'):
        index, value = sstore_state.mstate.stack[-1], sstore_state.mstate.stack[-2]
        try:
            index = helper.get_concrete_int(index)
        except AttributeError:
            index = str(index)
        if "storage_{}".format(index) not in interesting_storages:
            continue

        yield sstore_state, node

# TODO: remove
def _try_constraints(constraints, new_constraints):
    """
    Tries new constraints
    :return Model if satisfiable otherwise None
    """
    _constraints = copy.deepcopy(constraints)
    for constraint in new_constraints:
        _constraints.append(copy.deepcopy(constraint))
    try:
        model = solver.get_model(_constraints)
        return model
    except UnsatError:
        return None
