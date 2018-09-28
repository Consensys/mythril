import logging
import re

from mythril.analysis import solver
from mythril.analysis.ops import *
from mythril.analysis.report import Issue
from mythril.exceptions import UnsatError

'''
MODULE DESCRIPTION:
This module finds the existance of transaction order dependence vulnerabilities.
The following webpage contains an extensive description of the vulnerability: 
https://consensys.github.io/smart-contract-best-practices/known_attacks/#transaction-ordering-dependence-tod-front-running
'''


def execute(statespace):
    """ Executes the analysis module"""
    logging.debug("Executing module: TOD")

    issues = []

    for call in statespace.calls:
        # Do analysis
        interesting_storages = list(_get_influencing_storages(call))
        changing_sstores = list(_get_influencing_sstores(statespace, interesting_storages))

        # Build issue if necessary
        if len(changing_sstores) > 0:
            node = call.node
            instruction = call.state.get_current_instruction()
            issue = Issue(node.contract_name, node.function_name, instruction['address'],
                          "Transaction order dependence",
                          "Warning")

            issue.description = \
                "A possible transaction order dependence vulnerability exists in function {}. The value or " \
                "direction of the call statement is determined from a tainted storage location"\
                .format(node.function_name)
            issues.append(issue)

    return issues


# TODO: move to __init__ or util module
def _get_states_with_opcode(statespace, opcode):
    """ Gets all (state, node) tuples in statespace with opcode"""
    for k in statespace.nodes:
        node = statespace.nodes[k]
        for state in node.states:
            if state.get_current_instruction()["opcode"] == opcode:
                yield state, node


def _dependent_on_storage(expression):
    """ Checks if expression is dependent on a storage symbol and returns the influencing storages"""
    pattern = re.compile(r"storage_[a-z0-9_&^]*[0-9]+")
    return pattern.findall(str(simplify(expression)))


def _get_storage_variable(storage, state):
    """
    Get storage z3 object given storage name and the state
    :param storage: storage name example: storage_0
    :param state: state to retrieve the variable from
    :return: z3 object representing storage
    """
    index = int(re.search('[0-9]+', storage).group())
    try:
        return state.environment.active_account.storage[index]
    except KeyError:
        return None


def _can_change(constraints, variable):
    """ Checks if the variable can change given some constraints """
    _constraints = copy.deepcopy(constraints)
    try:
        model = solver.get_model(_constraints)
    except UnsatError:
        return False
    try:
        initial_value = int(str(model.eval(variable, model_completion=True)))
        return _try_constraints(constraints, [variable != initial_value]) is not None
    except AttributeError:
        return False

def _get_influencing_storages(call):
    """ Examines a Call object and returns an iterator of all storages that influence the call value or direction"""
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


def _get_influencing_sstores(statespace, interesting_storages):
    """ Gets sstore (state, node) tuples that write to interesting_storages"""
    for sstore_state, node in _get_states_with_opcode(statespace, 'SSTORE'):
        index, value = sstore_state.mstate.stack[-1], sstore_state.mstate.stack[-2]
        try:
            index = util.get_concrete_int(index)
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
