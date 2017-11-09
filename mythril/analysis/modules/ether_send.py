from z3 import *
from mythril.analysis.ops import *
from mythril.analysis import solver
from mythril.analysis.report import Issue
from mythril.exceptions import UnsatError
import re
import logging


'''
MODULE DESCRIPTION:

Check for CALLs that send >0 Ether to either the transaction sender, or to an address provided as a function argument.
If msg.sender is checked against a value in storage, check whether that storage index is tainted (i.e. there's an unconstrained write
to that index).
'''

def execute(statespace):

    issues = []

    for call in statespace.calls:

        if ("callvalue" in str(call.value)):
            logging.debug("[ETHER_SEND] Skipping refund function")
            continue

        logging.debug("[ETHER_SEND] CALL with value " + str(call.value.val))
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

        issue.description += "Call value is " + str(call.value) + "\n"

        if interesting:

            node = call.node

            constrained = False
            can_solve = True

            while (can_solve and len(node.constraints)):

                constraint = node.constraints.pop()

                m = re.search(r'storage_([a-z0-9_&^]+)', str(constraint))

                overwrite = False

                if (m):
                    constrained = True
                    index = m.group(1)

                    try:

                        for s in statespace.sstors[index]:

                            if s.tainted:
                                issue.description += "\nThere is a check on storage index " + str(index) + ". This storage index can be written to by calling the function '" + s.node.function_name + "'."
                                break

                        if not overwrite:
                            logging.debug("[ETHER_SEND] No storage writes to index " + str(index))
                            can_solve = False
                            break

                    except KeyError:
                        logging.debug("[ETHER_SEND] No storage writes to index " + str(index))
                        can_solve = False
                        break


                # CALLER may also be constrained to hardcoded address. I.e. 'caller' and some integer

                elif (re.search(r"caller", str(constraint)) and re.search(r'[0-9]{20}', str(constraint))):
                   can_solve = False
                   break


            if not constrained:
                issue.description += "\nIt seems that this function can be called without restrictions."

            if can_solve:

                try:
                    model = solver.get_model(node.constraints)
                    issues.append(issue)

                    for d in model.decls():
                        logging.debug("[ETHER_SEND] main model: %s = 0x%x" % (d.name(), model[d].as_long()))
                except UnsatError:
                        logging.debug("[ETHER_SEND] no model found")  

    return issues
