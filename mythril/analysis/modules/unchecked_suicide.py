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

                constraint_on_caller = None

                for constraint in node.constraints:
                    if "caller" in str(constraint):
                        m = re.search(r'storage_([0-9a-f])+', str(constraint))
                        cc_storage_index = m.group(1)
                        constraint_on_caller = constraint
                        break

                can_solve = False

                if constraint_on_caller is not None:

                    logging.info("caller constraint storage index " + cc_storage_index)

                    # Is there any way to write to that storage slot?

                    try:
                        sstors = statespace.tainted_sstors[cc_storage_index]

                        for sstor in sstors:

                            s = Solver()

                            for constraint in sstor.node.constraints:
                                s.add(constraint)

                            if (s.check() == sat):
                                m = s.model()

                                issue.description += "The transaction sender is checked against a value in storage index " + str(cc_storage_index) + ". However, it may be possible to overwrite this value by calling the function '" + sstor.node.function_name + "'."

                                can_solve = True
                                break
                    except KeyError:
                        logging.debug("No viable storage writes to index " + cc_storage_index)
                        can_solve = False

                else:
                    issue.description = "There are no restrictions on msg.sender."
                    can_solve = True

                if can_solve:

                    s = Solver()

                    for constraint in node.constraints:
                        s.add(constraint)

                    if (s.check() == sat):

                        if ("caller" in str(to)):
                            issue.description += "\nThe remaining Ether is sent to the caller's address.\n"
                        elif ("storage" in str(to)):
                            issue.description += "\nThe remaining Ether is sent to a stored address\n"
                        else:
                            issue.description += "\nThe remaining Ether is sent to: " + str(to) + "\n"

                        issue.description += "Solver output:\n"

                        m = s.model()

                        logging.debug("Model for node " + str(k) + ", function " +  svm.nodes[k].function_name + ": ")

                        for d in m.decls():
                            logging.debug("%s = 0x%x" % (d.name(), m[d].as_long()))

                        issues.append(issue)

    return issues
