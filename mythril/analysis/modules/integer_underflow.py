from z3 import *
from mythril.analysis import solver
from mythril.analysis.ops import *
from mythril.analysis.report import Issue
from mythril.exceptions import UnsatError
import re
import logging



'''
MODULE DESCRIPTION:

Check for integer underflows.
For every SUB instruction, check if there's a possible state where op1 > op0.
'''

def execute(statespace):

    issues = []

    for k in statespace.nodes:
        node = statespace.nodes[k]

        for instruction in node.instruction_list:

            if(instruction['opcode'] == "SUB"):

                stack = node.states[instruction['address']].stack

                op0 = stack[-1]
                op1 = stack[-2]

                constraints = node.constraints

                if (type(op0) == int and type(op1) == int):
                    continue

                logging.debug("[INTEGER_UNDERFLOW] Checking SUB " + str(op0) + ", " + str(op1))

                constraints.append(UGT(op1,op0))

                try:
                    
                    model = solver.get_model(node.constraints)

                    issue = Issue("Integer Underflow", "Warning")

                    m = re.search(r'(storage_\d+)', str(op0))

                    if (m):
                        storage_index = m.group(1)
                    else:
                        storage_index = "unknown"

                    issue.description = "A possible integer underflow exists in the function " + node.function_name + ".\n" \
                        "There SUB instruction at address " + str(instruction['address']) + " may underflow the state variable stored at position " + storage_index + "."

                    issues.append(issue)

                    for d in model.decls():
                        logging.debug("[INTEGER_UNDERFLOW] model: %s = 0x%x" % (d.name(), model[d].as_long()))

                except UnsatError:
                    logging.debug("[INTEGER_UNDERFLOW] no model found")         

    return issues
