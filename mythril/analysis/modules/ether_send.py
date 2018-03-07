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

    logging.debug("Executing module: ETHER_SEND")

    issues = []

    for call in statespace.calls:

        if ("callvalue" in str(call.value)):
            logging.debug("[ETHER_SEND] Skipping refund function")
            continue

        # We're only interested in calls that send Ether

        if call.value.type == VarType.CONCRETE:
            if call.value.val == 0:
                continue

        interesting = False

        description = "In the function '" + call.node.function_name +"' "

        if re.search(r'caller', str(call.to)):
            description += "a non-zero amount of Ether is sent to msg.sender.\n"
            interesting = True

        elif re.search(r'calldata', str(call.to)):
            description += "a non-zero amount of Ether is sent to an address taken from function arguments.\n"
            interesting = True

        else:
            m = re.search(r'storage_([a-z0-9_&^]+)', str(call.to))

            if (m):
                idx = m.group(1)

                func = statespace.find_storage_write(idx)

                if (func):
                    description += "\nThere is a check on storage index " + str(idx) + ". This storage slot can be written to by calling the function '" + func + "'.\n"
                    interesting = True
                else:
                    logging.debug("[ETHER_SEND] No storage writes to index " + str(idx))

        if interesting:

            node = call.node

            can_solve = True
            constrained = False

            index = 0

            while(can_solve and index < len(node.constraints)):

                constraint = node.constraints[index]
                index += 1
                logging.debug("[ETHER_SEND] Constraint: " + str(constraint))

                m = re.search(r'storage_([a-z0-9_&^]+)', str(constraint))

                if (m):

                    constrained = True
                    idx = m.group(1)

                    func = statespace.find_storage_write(idx)

                    if (func):
                        description += "\nThere is a check on storage index " + str(index) + ". This storage slot can be written to by calling the function '" + func + "'."
                    else:
                        logging.debug("[ETHER_SEND] No storage writes to index " + str(index))
                        can_solve = False
                        break

                # CALLER may also be constrained to hardcoded address. I.e. 'caller' and some integer

                elif (re.search(r"caller", str(constraint)) and re.search(r'[0-9]{20}', str(constraint))):
                    constrained = True
                    can_solve = False
                    break
        


            if not constrained:
                description += "It seems that this function can be called without restrictions."

            if can_solve:

                try:
                    model = solver.get_model(node.constraints)
                    logging.debug("[ETHER_SEND] MODEL: " + str(model))

                    for d in model.decls():
                        logging.debug("[ETHER_SEND] main model: %s = 0x%x" % (d.name(), model[d].as_long()))

                    issue = Issue(call.node.contract_name, call.node.function_name, call.addr, "Ether send", "Warning", description)
                    issues.append(issue)
 
                except UnsatError:
                    logging.debug("[ETHER_SEND] no model found")  

    return issues
