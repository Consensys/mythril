from z3 import *
from mythril.analysis.ops import *
from mythril.analysis.report import Issue
import re
import logging


'''
MODULE DESCRIPTION:

Check for SUICIDE instructions that are not constrained by caller
'''

def execute(statespace):

    issues = []

    svm = statespace.svm

    for k in svm.nodes:
        node = svm.nodes[k]

        for instruction in node.instruction_list:

            if(instruction['opcode'] == "SUICIDE"):

                issue = Issue("Unchecked SUICIDE", "VULNERABILITY")
                issue.description = "The function " + node.function_name + " calls the SUICIDE instruction. "

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
                                can_solve = True
                                break
                    except KeyError:
                        logging.info("No viable storage writes to index " + cc_storage_index)
                        can_solve = False

                else:
                    can_solve = True

                if can_solve:

                    for constraint in node.constraints:
                        s.add(constraint)

                    if (s.check() == sat):
                        issue = Issue("Unchecked SUICIDE", "VULNERABILITY")
                        issue.description = "The function " + node.function_name + " calls the SUICIDE instruction. It appears as if the function does not check the caller address.\n"

                        if ("caller" in str(to)):
                            issue.description += "The remaining Ether is sent to the caller's address.\n"
                        elif ("storage" in str(to)):
                            issue.description += "The remaining Ether is sent to a stored address\n"
                        else:
                            issue.description += "The remaining Ether is sent to: " + str(to) + "\n"

                        issue.description += "Solver output:\n"

                        m = s.model()

                        for d in m.decls():
                            issue.description += "%s = 0x%x\n" % (d.name(), m[d].as_long())

                    issues.append(issue)



    return issues
