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

                logging.debug("[INTEGER_UNDERFLOW] Checking SUB " + str(op0) + ", " + str(op1) + " at address " + str(instruction['address']))

                constraints.append(UGT(op1,op0))

                try:
                    
                    model = solver.get_model(node.constraints)

                    issue = Issue("Integer Underflow", "Warning")

                    op0 = str(op0).replace("\n","")
                    op1 = str(op1).replace("\n","")

                    issue.description = "A possible integer underflow exists in the function " + node.function_name + ".\n" \
                        "There SUB instruction at address " + str(instruction['address']) + " performs the operation " + str(op0) + " - " + str(op1) + ". " \
                        "However, it is not verified that " + str(op0) + " >= " + str(op1) + "."

                    issues.append(issue)

                    for d in model.decls():
                        logging.debug("[INTEGER_UNDERFLOW] model: %s = 0x%x" % (d.name(), model[d].as_long()))

                except UnsatError:
                    logging.debug("[INTEGER_UNDERFLOW] no model found")         

    return issues
