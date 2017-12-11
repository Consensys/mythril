from z3 import *
from mythril.analysis import solver
from mythril.analysis.ops import *
from mythril.analysis.report import Issue
from mythril.exceptions import UnsatError
import copy
import re
import logging


UINT_MAX = BitVecVal(2 ** 256 - 1, 256)


'''
MODULE DESCRIPTION:

Check for integer overflows.
Checks ADD instruction, MUL still todo
'''

def execute(statespace):

    issues = []

    for k in statespace.nodes:
        node = statespace.nodes[k]

        for instruction in node.instruction_list:

            if(instruction['opcode'] == "ADD"):

                stack = node.states[instruction['address']].stack

                op0 = stack[-1]
                op1 = stack[-2]

                if type(op0) == int and type(op1) == int:
                    continue

                logging.debug("[INTEGER_OVERFLOW] Checking ADD " + str(op0) + ", " + str(op1) + " at address " + str(instruction['address']))

                constraints = copy.deepcopy(node.constraints)

                constraints.append(UGT(op0, UINT_MAX - op1))

                try:
                    
                    model = solver.get_model(constraints)

                    issue = Issue(node.module_name, node.function_name, instruction['address'], "Integer Overflow", "Warning")

                    issue.description = "A possible integer overflow exists in the function " + node.function_name + ".\n" \
                        "The addition at address " + str(instruction['address']) + " may result in a value greater than UINT_MAX." 

                    issue.debug = "(" + str(op0) + ") + (" + str(op1) + ") > (" + hex(UINT_MAX.as_long()) + ")"

                    issues.append(issue)

                    for d in model.decls():
                        logging.debug("[INTEGER_OVERFLOW] model: %s = 0x%x" % (d.name(), model[d].as_long()))

                except UnsatError:
                    logging.debug("[INTEGER_OVERFLOW] no model found")   

            elif(instruction['opcode'] == "MUL"):

                stack = node.states[instruction['address']].stack

                op0 = stack[-1]
                op1 = stack[-2]

                if (type(op0) == int and type(op1) == int) or type(op0) == BoolRef:
                    continue

                logging.debug("[INTEGER_OVERFLOW] Checking MUL " + str(op0) + ", " + str(op1) + " at address " + str(instruction['address']))

                if (re.search(r'146150163733', str(op0), re.DOTALL) or re.search(r'146150163733', str(op1), re.DOTALL)):


                    continue

                constraints = copy.deepcopy(node.constraints)

                constraints.append(UGT(op0, UINT_MAX / op1))

                try:
                    
                    model = solver.get_model(constraints)

                    issue = Issue(node.module_name, node.function_name, instruction['address'], "Integer Overflow", "Warning")

                    issue.description = "A possible integer overflow exists in the function " + node.function_name + ".\n" \
                        "The multiplication at address " + str(instruction['address']) + " may result in a value greater than UINT_MAX." 

                    issue.debug = "(" + str(op0) + ") * (" + str(op1) + ") > (" + hex(UINT_MAX.as_long()) + ")"

                    issues.append(issue)

                    for d in model.decls():
                        logging.debug("[INTEGER_OVERFLOW] model: %s = 0x%x" % (d.name(), model[d].as_long()))

                except UnsatError:
                    logging.debug("[INTEGER_OVERFLOW] no model found")   

    return issues
