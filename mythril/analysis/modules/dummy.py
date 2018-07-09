from mythril.analysis.report import Issue
import logging
from z3 import *
from mythril.solidnotary.z3utility import simplify_constraints, are_satisfiable


'''
    To print content of the statespace after it was build.
'''

def print_obj(obj):
    print()
    print(obj)
    print(type(obj))
    print(dir(obj))
    print()


def execute(statespace):

    logging.debug("Executing module: Transaction End")

    issues = []

#    for k in statespace.nodes:
#        node = statespace.nodes[k]

#        for state in node.states:

#            instruction = state.get_current_instruction()

#            if(instruction['opcode'] == "STOP"):
#                print()
                #print(state.environment.active_account.storage)
                # print(state.mstate.constraints)
                #simpl_const = simplify_constraints(state.mstate.constraints)
                #print(simpl_const)
                #print(are_satisfiable(simpl_const))
                # print("opc: {}, add: {} {}".format(instruction['opcode'], instruction['address'], instruction['argument'] if 'argument' in instruction else ""))

    return issues
