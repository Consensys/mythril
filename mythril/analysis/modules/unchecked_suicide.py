from z3 import *
from mythril.analysis.ops import *
from mythril.analysis.report import Issue
import re
import logging


'''
MODULE DESCRIPTION:

Check for SUICIDE instructions that either can be reached by anyone, or where msg.sender is checked against a writable storage index.
'''

def execute(statespace):

    issues = []

    svm = statespace.svm

    for k in svm.nodes:
        node = svm.nodes[k]

        for instruction in node.instruction_list:

            if(instruction['opcode'] == "SUICIDE"):

                issue = Issue("Unchecked SUICIDE", "Warning")
                issue.description = "The function " + node.function_name + " executes the SUICIDE instruction."

                state = node.states[instruction['address']]
                to = state.stack.pop()

                if ("caller" in str(to)):
                    issue.description += "\nThe remaining Ether is sent to the caller's address.\n"
                elif ("storage" in str(to)):
                    issue.description += "\nThe remaining Ether is sent to a stored address\n"
                else:
                    issue.description += "\nThe remaining Ether is sent to: " + str(to) + "\n"

                for constraint in node.constraints:
                    m = re.search(r'storage_([0-9a-f])+', str(constraint))

                    can_solve = True

                    if (m):
                        index = m.group(1)

                        try:
                            can_write = False

                            for s in statespace.sstors[index]:
                                if s.tainted:
                                    can_write = True

                                    issue.description += "There is a check on storage index " + str(index) + ". This storage index can be written to by calling the function '" + s.node.function_name + "'."
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

                    s = Solver()

                    for constraint in node.constraints:
                        # print(str(constraint))
                        s.add(constraint)

                    if (s.check() == sat):

                        m = s.model()

                        logging.debug("Model for node " + str(node.uid) + ", function " +  node.function_name + ": ")

                        for d in m.decls():
                            logging.debug("%s = 0x%x" % (d.name(), m[d].as_long()))

                        issues.append(issue)


    return issues
