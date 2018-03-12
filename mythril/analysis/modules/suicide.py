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

    logging.debug("Executing module: UNCHECKED_SUICIDE")

    issues = []

    for k in statespace.nodes:
        node = statespace.nodes[k]

        for state in node.states:

            instruction = state.get_current_instruction()

            if(instruction['opcode'] == "SUICIDE"):

                logging.debug("[UNCHECKED_SUICIDE] suicide in function " + node.function_name)

                description = "The function " + node.function_name + " executes the SUICIDE instruction. "

                stack = copy.deepcopy(state.mstate.stack)
                to = stack.pop()

                if ("caller" in str(to)):
                    description += "The remaining Ether is sent to the caller's address."
                elif ("storage" in str(to)):
                    description += "The remaining Ether is sent to a stored address."
                elif ("calldata" in str(to)):
                    description += "The remaining Ether is sent to an address provided as a function argument."
                elif (type(to) == BitVecNumRef):
                    description += "The remaining Ether is sent to: " + hex(to.as_long())
                else:
                    description += "The remaining Ether is sent to: " + str(to) + "\n"

                constrained = False
                can_solve = True

                index = 0

                while(can_solve and index < len(node.constraints)):

                    constraint = node.constraints[index]
                    index += 1

                    m = re.search(r'storage_([a-z0-9_&^]+)', str(constraint))

                    overwrite = False

                    if (m):
                        constrained = True
                        idx = m.group(1)

                        logging.debug("STORAGE CONSTRAINT FOUND: " + idx)

                        func = statespace.find_storage_write(idx)

                        if func:
                            description += "\nThere is a check on storage index " + str(index) + ". This storage index can be written to by calling the function '" + func + "'."
                            break
                        else:
                            logging.debug("[UNCHECKED_SUICIDE] No storage writes to index " + str(idx))
                            can_solve = False
                            break


                    # CALLER may also be constrained to hardcoded address. I.e. 'caller' and some integer

                    elif (re.search(r"caller", str(constraint)) and re.search(r'[0-9]{20}', str(constraint))):
                       can_solve = False
                       break


                if not constrained:
                    description += "\nIt seems that this function can be called without restrictions."

                if can_solve:

                    try:
                        model = solver.get_model(node.constraints)
                        logging.debug("[UNCHECKED_SUICIDE] MODEL: " + str(model))


                        for d in model.decls():
                            logging.debug("[UNCHECKED_SUICIDE] main model: %s = 0x%x" % (d.name(), model[d].as_long()))

                        issue = Issue(node.contract_name, node.function_name, instruction['address'], "Unchecked SUICIDE", "Warning", description)
                        issues.append(issue)

                    except UnsatError:
                            logging.debug("[UNCHECKED_SUICIDE] no model found")    

    return issues
