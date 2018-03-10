from mythril.analysis.report import Issue
from mythril.exceptions import UnsatError
from mythril.analysis import solver
from z3 import simplify
import logging


'''
MODULE DESCRIPTION:

Check for constraints on tx.origin (i.e., access to some functionality is restricted to a specific origin).
'''


def execute(statespace):

    logging.debug("Executing module: ASSERT_VIOLATION")

    issues = []

    for k in statespace.nodes:
        node = statespace.nodes[k]

        for state in node.states:

            instruction = state.get_current_instruction()

            if(instruction['opcode'] == "ASSERT_VIOLATION"):

                try:
                    model = solver.get_model(node.constraints)
                    logging.debug("[ASSERT_VIOLATION ASSERT] MODEL: " + str(model))

                    address = state.get_current_instruction()['address']

                    description = "Invalid opcode reached (0xfe). can be caused by a possible type error, out-of-bounds array access, or assert violation.\n\n"

                    description = "Variable values:\n\n"

                    for d in model.decls():

                        try:
                            condition = hex(model[d].as_long())
                        except:
                            condition = str(simplify(model[d]))

                        description += ("%s: %s\n" % (d.name(), condition))

                    description += "\n\nNote that assert() should only be used to check invariants. Use require() for regular input checking."

                    issues.append(Issue(node.contract_name, node.function_name, address, "Assertion violation", description))

                except UnsatError:
                    logging.debug("[FAILED ASSERT] no model found")

    return issues
