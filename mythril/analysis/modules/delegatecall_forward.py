from z3 import *
import re
from mythril.analysis.ops import *
from mythril.analysis.report import Issue


'''
MODULE DESCRIPTION:

Check for invocations of delegatecall(msg.data) in the fallback function.
'''

def execute(statespace):

    issues = []

    for call in statespace.calls:

        if (call.type == "DELEGATECALL") and (call.node.function_name == "main"):

            stack = call.state.stack

            meminstart = get_variable(stack[-3])

            if meminstart.type == VarType.CONCRETE:

                if (re.search(r'calldata.*_0', str(call.state.memory[meminstart.val]))):

                    issue = Issue("CALLDATA forwarded with delegatecall()", "INFORMATION")
                    issue.description = \
                        "The contract '" +  str(call.node.module_name)  + "' forwards its calldata via DELEGATECALL in its fallback function. " \
                        "This means that any function in the called contract can be executed. Make sure to scan with the -l option so dependencies are checked as well.\n"      
                    
                    if (call.to.type == VarType.CONCRETE):
                        issue.description += ("DELEGATECALL target: " + hex(call.to.val))
                    else:
                        issue.description += "DELEGATECALL target: " + str(call.to)

                    issues.append(issue)

    return issues
