from z3 import *
from mythril.analysis import solver
from mythril.analysis.ops import *
from mythril.analysis.report import Issue
from mythril.exceptions import UnsatError
import re
import copy
import logging

'''
MODULE DESCRIPTION:

Check for integer underflows.
For every SUB instruction, check if there's a possible state where op1 > op0.
For every ADD instruction, check if there's a possible state where op1 + op0 > 2^32 - 1 
'''


def execute(statespace):
    """
    Executes analysis module for integer underflow and integer overflow
    :param statespace: Statespace to analyse
    :return: Found issues
    """
    logging.debug("Executing module: INTEGER")

    issues = []

    for k in statespace.nodes:
        node = statespace.nodes[k]

        for state in node.states:
            logging.debug("Checking for integer underflow")
            issues += _check_integer_underflow(state, node)
            logging.debug("Checking for integer overflow")
            issues += _check_integer_overflow(statespace, state, node)

    return issues


def _check_integer_overflow(statespace, state, node):
    """
    Checks for integer overflow
    :param statespace: statespace that is being examined
    :param state: state from node to examine
    :param node: node to examine
    :return: found issue
    """
    issues = []

    # Check the instruction
    instruction = state.get_current_instruction()
    if instruction['opcode'] != "ADD":
        return []

    constraints = copy.deepcopy(node.constraints)

    # Formulate overflow constraints
    stack = state.mstate.stack
    op0, op1 = stack[-1], stack[-2]

    # An integer overflow is possible if op0 + op1,
    constraints.append(UGT(op0 + op1, (2 ** 32) - 1))

    try:
        model = solver.get_model(constraints)

        # If we get to this point then there has been an integer overflow
        # Find out if the overflowed value is actually used
        interesting_usages = _search_children(statespace, node, (op0 + op1), index=node.states.index(state))

        # Stop if it isn't
        if len(interesting_usages) == 0:
            return issues

        issue = Issue(node.contract_name, node.function_name, instruction['address'], "Integer Overflow ",
                      "Warning")

        issue.description = "A possible integer overflow exists in the function {}.\n" \
                            "The addition may result in a value higher than the maximum representable integer.".format(node.function_name)
        issue.debug = solver.pretty_print_model(model)
        issues.append(issue)

    except UnsatError:
        logging.debug("[INTEGER_OVERFLOW] no model found")

    return issues


def _check_integer_underflow(state, node):
    """
    Checks for integer underflow
    :param state: state from node to examine
    :param node: node to examine
    :return: found issue
    """
    issues = []
    instruction = state.get_current_instruction()

    if instruction['opcode'] == "SUB":

        stack = state.mstate.stack

        op0 = stack[-1]
        op1 = stack[-2]

        constraints = copy.deepcopy(node.constraints)

        # Filter for patterns that contain bening nteger underflows.

        # Pattern 1: (96 + calldatasize_MAIN) - (96), where (96 + calldatasize_MAIN) would underflow if calldatasize is very large.
        # Pattern 2: (256*If(1 & storage_0 == 0, 1, 0)) - 1, this would underlow if storage_0 = 0
        if type(op0) == int and type(op1) == int:
            return []
        if re.search(r'calldatasize_', str(op0)):
            return []
        if re.search(r'256\*.*If\(1', str(op0), re.DOTALL) or re.search(r'256\*.*If\(1', str(op1), re.DOTALL):
            return []
        if re.search(r'32 \+.*calldata', str(op0), re.DOTALL) or re.search(r'32 \+.*calldata', str(op1), re.DOTALL):
            return []

        logging.debug("[INTEGER_UNDERFLOW] Checking SUB {0}, {1} at address {2}".format(str(op0), str(op1),
                                                                                        str(instruction['address'])))

        allowed_types = [int, BitVecRef, BitVecNumRef]

        if type(op0) in allowed_types and type(op1) in allowed_types:
            constraints.append(UGT(op1, op0))

            try:

                model = solver.get_model(constraints)

                issue = Issue(node.contract_name, node.function_name, instruction['address'], "Integer Underflow",
                              "Warning")

                issue.description = "A possible integer underflow exists in the function " + node.function_name + ".\n" \
                                                                                                                  "The subtraction may result in a value < 0."

                issue.debug = solver.pretty_print_model(model)
                issues.append(issue)

            except UnsatError:
                logging.debug("[INTEGER_UNDERFLOW] no model found")
    return issues


def _check_usage(state, expression):
    """Delegates checks to _check_{instruction_name}()"""
    opcode = state.get_current_instruction()['opcode']

    if opcode == 'JUMPI':
        if _check_jumpi(state, expression):
            return [state]
    elif opcode == 'SSTORE':
        if _check_sstore(state, expression):
            return [state]
    return []


def _check_jumpi(state, expression):
    """ Check if conditional jump is dependent on the result of expression"""
    assert state.get_current_instruction()['opcode'] is 'JUMPI'
    condition = state.mstate.stack[-2]
    return str(expression) in str(condition)


def _check_sstore(state, expression):
    """ Check if store operation is dependent on the result of expression"""
    assert state.get_current_instruction()['opcode'] is 'SSTORE'
    value = state.mstate.stack[-2]
    return str(expression) in str(value)


def _search_children(statespace, node, expression, index=0, depth=0, max_depth=64):
    """
    Checks the statespace for children states, with JUMPI or SSTORE instuctions,
    for dependency on expression
    :param statespace: The statespace to explore
    :param node: Current node to explore from
    :param expression: Expression to look for
    :param index: Current state index node.states[index] == current_state
    :param depth: Current depth level
    :param max_depth: Max depth to explore
    :return: List of states that match the opcodes and are dependent on expression
    """
    logging.debug("SEARCHING NODE for usage of an overflowed variable %d", node.uid)

    results = []

    if depth >= max_depth:
        return []

    # Explore current node from index
    for j in range(index, len(node.states)):
        current_state = node.states[j]
        current_instruction = current_state.get_current_instruction()
        if current_instruction['opcode'] in ('JUMPI', 'SSTORE'):
            results += _check_usage(current_state, expression)

    # Recursively search children
    children = [statespace.nodes[edge.node_to] for edge in statespace.edges if edge.node_from == node.uid]
    for child in children:
        results += _search_children(statespace, child, expression, depth=depth+1, max_depth=max_depth)

    return results

