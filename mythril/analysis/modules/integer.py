from z3 import *
from mythril.analysis import solver
from mythril.analysis.ops import *
from mythril.analysis.report import Issue
from mythril.analysis.swc_data import INTEGER_OVERFLOW_AND_UNDERFLOW
from mythril.exceptions import UnsatError
from mythril.laser.ethereum.taint_analysis import TaintRunner
import re
import copy
import logging

"""
MODULE DESCRIPTION:

Check for integer underflows.
For every SUB instruction, check if there's a possible state where op1 > op0.
For every ADD, MUL instruction, check if there's a possible state where op1 + op0 > 2^32 - 1
"""


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
            issues += _check_integer_underflow(statespace, state, node)
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
    if instruction["opcode"] not in ("ADD", "MUL"):
        return issues

    # Formulate overflow constraints
    stack = state.mstate.stack
    op0, op1 = stack[-1], stack[-2]

    # An integer overflow is possible if op0 + op1 or op0 * op1 > MAX_UINT
    # Do a type check
    allowed_types = [int, BitVecRef, BitVecNumRef]
    if not (type(op0) in allowed_types and type(op1) in allowed_types):
        return issues

    # Change ints to BitVec
    if type(op0) is int:
        op0 = BitVecVal(op0, 256)
    if type(op1) is int:
        op1 = BitVecVal(op1, 256)

    # Formulate expression
    if instruction["opcode"] == "ADD":
        expr = op0 + op1
    else:
        expr = op1 * op0

    # Check satisfiable
    constraint = Or(And(ULT(expr, op0), op1 != 0), And(ULT(expr, op1), op0 != 0))
    model = _try_constraints(node.constraints, [constraint])

    if model is None:
        logging.debug("[INTEGER_OVERFLOW] no model found")
        return issues

    if not _verify_integer_overflow(
        statespace, node, expr, state, model, constraint, op0, op1
    ):
        return issues

    # Build issue
    issue = Issue(
        contract=node.contract_name,
        function_name=node.function_name,
        address=instruction["address"],
        swc_id=INTEGER_OVERFLOW_AND_UNDERFLOW,
        bytecode=state.environment.code.bytecode,
        title="Integer Overflow",
        _type="Warning",
    )

    issue.description = "The arithmetic operation can result in integer overflow.\n"
    issue.debug = "Transaction Sequence: " + str(
        solver.get_transaction_sequence(state, node.constraints)
    )
    issues.append(issue)

    return issues


def _verify_integer_overflow(
    statespace, node, expr, state, model, constraint, op0, op1
):
    """ Verifies existence of integer overflow """
    # If we get to this point then there has been an integer overflow
    # Find out if the overflowed value is actually used
    interesting_usages = _search_children(
        statespace, node, expr, constraint=[constraint], index=node.states.index(state)
    )

    # Stop if it isn't
    if len(interesting_usages) == 0:
        return False

    return _try_constraints(node.constraints, [Not(constraint)]) is not None


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


def _check_integer_underflow(statespace, state, node):
    """
    Checks for integer underflow
    :param state: state from node to examine
    :param node: node to examine
    :return: found issue
    """
    issues = []
    instruction = state.get_current_instruction()
    if instruction["opcode"] == "SUB":

        stack = state.mstate.stack

        op0 = stack[-1]
        op1 = stack[-2]

        constraints = copy.deepcopy(node.constraints)

        # Filter for patterns that indicate benign underflows

        # Pattern 1: (96 + calldatasize_MAIN) - (96), where (96 + calldatasize_MAIN) would underflow if calldatasize is very large.
        # Pattern 2: (256*If(1 & storage_0 == 0, 1, 0)) - 1, this would underlow if storage_0 = 0
        if type(op0) == int and type(op1) == int:
            return []
        if re.search(r"calldatasize_", str(op0)):
            return []
        if re.search(r"256\*.*If\(1", str(op0), re.DOTALL) or re.search(
            r"256\*.*If\(1", str(op1), re.DOTALL
        ):
            return []
        if re.search(r"32 \+.*calldata", str(op0), re.DOTALL) or re.search(
            r"32 \+.*calldata", str(op1), re.DOTALL
        ):
            return []

        logging.debug(
            "[INTEGER_UNDERFLOW] Checking SUB {0}, {1} at address {2}".format(
                str(op0), str(op1), str(instruction["address"])
            )
        )
        allowed_types = [int, BitVecRef, BitVecNumRef]

        if type(op0) in allowed_types and type(op1) in allowed_types:
            constraints.append(UGT(op1, op0))

            try:

                model = solver.get_model(constraints)

                # If we get to this point then there has been an integer overflow
                # Find out if the overflowed value is actually used
                interesting_usages = _search_children(
                    statespace, node, (op0 - op1), index=node.states.index(state)
                )

                # Stop if it isn't
                if len(interesting_usages) == 0:
                    return issues

                issue = Issue(
                    contract=node.contract_name,
                    function_name=node.function_name,
                    address=instruction["address"],
                    swc_id=INTEGER_OVERFLOW_AND_UNDERFLOW,
                    bytecode=state.environment.code.bytecode,
                    title="Integer Underflow",
                    _type="Warning",
                )

                issue.description = (
                    "The subtraction can result in an integer underflow.\n"
                )

                issue.debug = "Transaction Sequence: " + str(
                    solver.get_transaction_sequence(state, node.constraints)
                )
                issues.append(issue)

            except UnsatError:
                logging.debug("[INTEGER_UNDERFLOW] no model found")
    return issues


def _check_usage(state, taint_result):
    """Delegates checks to _check_{instruction_name}()"""
    opcode = state.get_current_instruction()["opcode"]

    if opcode == "JUMPI":
        if _check_jumpi(state, taint_result):
            return [state]
    elif opcode == "SSTORE":
        if _check_sstore(state, taint_result):
            return [state]
    return []


def _check_jumpi(state, taint_result):
    """ Check if conditional jump is dependent on the result of expression"""
    assert state.get_current_instruction()["opcode"] == "JUMPI"
    return taint_result.check(state, -2)


def _check_sstore(state, taint_result):
    """ Check if store operation is dependent on the result of expression"""
    assert state.get_current_instruction()["opcode"] == "SSTORE"
    return taint_result.check(state, -2)


def _search_children(
    statespace,
    node,
    expression,
    taint_result=None,
    constraint=None,
    index=0,
    depth=0,
    max_depth=64,
):
    """
    Checks the statespace for children states, with JUMPI or SSTORE instuctions,
    for dependency on expression
    :param statespace: The statespace to explore
    :param node: Current node to explore from
    :param expression: Expression to look for
    :param taint_result: Result of taint analysis
    :param index: Current state index node.states[index] == current_state
    :param depth: Current depth level
    :param max_depth: Max depth to explore
    :return: List of states that match the opcodes and are dependent on expression
    """
    if constraint is None:
        constraint = []

    logging.debug("SEARCHING NODE for usage of an overflowed variable %d", node.uid)

    if taint_result is None:
        state = node.states[index]
        taint_stack = [False for _ in state.mstate.stack]
        taint_stack[-1] = True
        taint_result = TaintRunner.execute(
            statespace, node, state, initial_stack=taint_stack
        )

    results = []

    if depth >= max_depth:
        return []

    # Explore current node from index
    for j in range(index, len(node.states)):
        current_state = node.states[j]
        current_instruction = current_state.get_current_instruction()
        if current_instruction["opcode"] in ("JUMPI", "SSTORE"):
            element = _check_usage(current_state, taint_result)
            if len(element) < 1:
                continue
            results += element

    # Recursively search children
    children = [
        statespace.nodes[edge.node_to]
        for edge in statespace.edges
        if edge.node_from == node.uid
        # and _try_constraints(statespace.nodes[edge.node_to].constraints, constraint) is not None
    ]

    for child in children:
        results += _search_children(
            statespace,
            child,
            expression,
            taint_result,
            depth=depth + 1,
            max_depth=max_depth,
        )

    return results
