from z3 import *
from mythril.analysis import solver
from mythril.analysis.ops import *
from mythril.analysis.report import Issue
from mythril.exceptions import UnsatError
import copy
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

                constraints = copy.deepcopy(node.constraints)

                if type(op0) == int and type(op1) == int:
                    continue

                logging.debug("[INTEGER_OVERFLOW] Checking ADD " + str(op0) + ", " + str(op1) + " at address " + str(instruction['address']))

                logging.debug("(" + str(op0) + ") > (" + hex(UINT_MAX.as_long()) + " - " + str(op1) + ")")

                constraints.append(UGT(op0, UINT_MAX - op1))

                try:
                    
                    model = solver.get_model(constraints)

                    issue = Issue(node.module_name, node.function_name, instruction['address'], "Integer Overflow", "Warning")

                    issue.description = "A possible integer overflow exists in the function " + node.function_name + ".\n" \
                        "The ADD instruction at address " + str(instruction['address']) + " may result in a value greater than UINT_MAX." 

                    issue.debug = "(" + str(op0) + ") > (" + hex(UINT_MAX.as_long()) + " - " + str(op1) + ")"

                    issues.append(issue)

                    for d in model.decls():
                        logging.debug("[INTEGER_OVERFLOW] model: %s = 0x%x" % (d.name(), model[d].as_long()))

                except UnsatError:
                    logging.debug("[INTEGER_OVERFLOW] no model found")   

    return issues
