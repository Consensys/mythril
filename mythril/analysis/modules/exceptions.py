from mythril.analysis.report import Issue
from mythril.exceptions import UnsatError
from mythril.analysis import solver
import logging


'''
MODULE DESCRIPTION:

Checks whether any exception states are reachable.

'''


def execute(statespace):

    logging.debug("Executing module: EXCEPTIONS")

    issues = []

    for k in statespace.nodes:
        node = statespace.nodes[k]

        for state in node.states:

            instruction = state.get_current_instruction()

            if(instruction['opcode'] == "ASSERT_FAIL"):

                try:
                    model = solver.get_model(node.constraints)
                    address = state.get_current_instruction()['address']

                    description = "A reachable exception (opcode 0xfe) has been detected. This can be caused by type errors, division by zero, out-of-bounds array access, or assert violations. "
                    description += "This is acceptable in most situations. Note however that assert() should only be used to check invariants. Use require() for regular input checking. "

                    debug = "The exception is triggered under the following conditions:\n\n"

                    debug += solver.pretty_print_model(model)

                    issues.append(Issue(node.contract_name, node.function_name, address, "Exception state", "Informational", description, debug))

                except UnsatError:
                    logging.debug("[EXCEPTIONS] no model found")

    return issues
