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

    logging.debug("Executing module: FAILED ASSERT")

    issues = []

    for k in statespace.nodes:
        node = statespace.nodes[k]

        for state in node.states:

            instruction = state.get_current_instruction()

            if(instruction['opcode'] == "ASSERT_FAIL"):

                try:
                    model = solver.get_model(node.constraints)
                    logging.debug("[FAILED ASSERT] MODEL: " + str(model))

                    for d in model.decls():
                        logging.debug("[FAILED ASSERT] main model: %s = 0x%x" % (d.name(), model[d].as_long()))

                    address = state.get_current_instruction()['address']

                    description = "It appears to be possible to violate the condition specified in a Solidity assert() statement. The violation is triggered with the following values:\n\n"

                    for d in model.decls():

                        try:
                            condition = hex(model[d].as_long())
                        except:
                            condition = str(simplify(model[d]))

                        description += ("%s: %s\n" % (d.name(), condition))

                    description += "\nNote that assert() should only be used to check invariants. Use require() for regular input checking."

                    issues.append(Issue(node.contract_name, node.function_name, address, "Assertion violation", description))

                except UnsatError:
                    logging.debug("[FAILED ASSERT] no model found")

    return issues
