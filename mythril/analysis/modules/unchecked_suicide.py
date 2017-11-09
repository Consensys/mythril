from z3 import *
from mythril.analysis import solver
from mythril.analysis.ops import *
from mythril.analysis.report import Issue
from mythril.exceptions import UnsatError
import re
import logging



'''
MODULE DESCRIPTION:

Check for SUICIDE instructions that either can be reached by anyone, or where msg.sender is checked against a tainted storage index 
(i.e. there's a write to that index is unconstrained by msg.sender).
'''

def execute(statespace):

    issues = []

    for k in statespace.nodes:
        node = statespace.nodes[k]

        for instruction in node.instruction_list:

            if(instruction['opcode'] == "SUICIDE"):

                logging.debug("[UNCHECKED SUICIDE] suicide in function " + node.function_name)

                issue = Issue("Unchecked SUICIDE", "Warning")
                issue.description = "The function " + node.function_name + " executes the SUICIDE instruction."

                state = node.states[instruction['address']]
                to = state.stack.pop()

                if ("caller" in str(to)):
                    issue.description += "\nThe remaining Ether is sent to the caller's address.\n"
                elif ("storage" in str(to)):
                    issue.description += "\nThe remaining Ether is sent to a stored address\n"
                elif ("calldata" in str(to)):
                    issue.description += "\nThe remaining Ether is sent to an address provided as a function argument."
                else:
                    issue.description += "\nThe remaining Ether is sent to: " + str(to) + "\n"

                for constraint in node.constraints:

                    m = re.search(r'storage_([a-z0-9_&^]+)', str(constraint))

                    can_solve = True

                    if (m):
                        index = m.group(1)

                        try:
                            can_write = False

                            for s in statespace.sstors[index]:

                                if s.tainted:
                                    can_write = True

                                    issue.description += "\nThere is a check on storage index " + str(index) + ". This storage index can be written to by calling the function '" + s.node.function_name + "'."
                                    break

                            if not can_write:
                                logging.info("No storage writes to index " + str(index))
                                can_solve = False
                                break

                        except KeyError:
                            logging.info("No storage writes to index " + str(index))
                            can_solve = False
                            break

                if can_solve:

                    try:
                        model = solver.get_model(node.constraints)
                        issues.append(issue)

                        for d in model.decls():
                            logging.debug("[UNCHECKED_SUICIDE] main model: %s = 0x%x" % (d.name(), model[d].as_long()))
                    except UnsatError:
                            logging.debug("[UNCHECKED_SUICIDE] no model found")         

    return issues
