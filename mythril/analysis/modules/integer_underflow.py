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

                if re.search(r'\d* \+ calldata', str(op0)) and re.search(r'\d+', str(op1)):
                    # Filter for a common pattern that contains an possible (but Ion-exploitable) Integer overflow and subsequent underflow.
                    # The pattern looks as follows: (96 + calldatasize_MAIN) - (96), where (96 + calldatasize_MAIN) would overflow if calldatasize is very large.
                    # There's a few other things that sometimes pop up which still need to be investigated.

                    continue

                logging.debug("[INTEGER_UNDERFLOW] Checking SUB " + str(op0) + ", " + str(op1) + " at address " + str(instruction['address']))

                constraints.append(UGT(op1,op0))

                try:
                    
                    model = solver.get_model(node.constraints)

                    op0 = str(op0).replace("\n","")
                    op1 = str(op1).replace("\n","")

                    issue = Issue(node.module_name, node.function_name, instruction['address'], "Integer Underflow", "Warning")

                    issue.description = "A possible integer underflow exists in the function " + node.function_name + ".\n" \
                        "The SUB instruction at address " + str(instruction['address']) + " may result in a value < 0." 

                    issue.debug = "(" + str(op0) + ") - (" + str(op1) + ").]"

                    issues.append(issue)

                    for d in model.decls():
                        logging.debug("[INTEGER_UNDERFLOW] model: %s = 0x%x" % (d.name(), model[d].as_long()))

                except UnsatError:
                    logging.debug("[INTEGER_UNDERFLOW] no model found")         

    return issues
