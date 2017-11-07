from z3 import *
from mythril.analysis.ops import *
from mythril.analysis.report import Issue
import re
import logging


'''
MODULE DESCRIPTION:

Check for CALLs that send >0 Ether to a chosen address.
Return locations that can be reached by anyone, or that have constraints on storage indices that can be written to.
'''

def execute(statespace):

    issues = []

    for call in statespace.calls:

        logging.debug("CALL with value " + str(call.value.val))
        issue = Issue("Ether send", "Warning")

        # We're only interested in calls that send Ether

        if call.value.type == VarType.CONCRETE:
            if call.value.val == 0:
                continue

        interesting = False

        issue.description = "In the function '" + call.node.function_name +"' "

        # Check the CALL target

        if re.search(r'caller', str(call.to)):
            issue.description += "a non-zero amount of Ether is sent to msg.sender.\n"
            interesting = True

        if re.search(r'calldata', str(call.to)):
            issue.description += "a non-zero amount of Ether is sent to an address taken from function arguments.\n"
            interesting = True

        if interesting:

            node = call.node

            can_solve = True

            for constraint in node.constraints:
                m = re.search(r'storage_([0-9a-f])+', str(constraint))

                if (m):
                    index = m.group(1)

                    write_func = statespace.find_storage_write(index)

                    if write_func is None:
                        can_solve = False
                        break

            if can_solve:

                s = Solver()

                for constraint in node.constraints:
                    s.add(constraint)

                if (s.check() == sat):

                    m = s.model()

                    logging.debug("Model for node " + str(node.uid) + ", function " +  node.function_name + ": ")

                    for d in m.decls():
                        logging.debug("%s = 0x%x" % (d.name(), m[d].as_long()))

                    issues.append(issue)

    return issues