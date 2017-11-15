from z3 import *
from mythril.analysis.ops import *
from mythril.analysis.report import Issue


'''
MODULE DESCRIPTION:

Check for invocations of delegatecall to a dynamic contract address (e.g. taken from storage).
'''

def execute(statespace):

    issues = []
    visited = []

    for call in statespace.calls:

        # Only needs to be checked once per call instructions (essentially just static analysis)

        if call.addr in visited:
            continue
        else:
            visited.append(call.addr)

        if (call.type == "DELEGATECALL"):

            if (call.to.type == VarType.SYMBOLIC):

                issue = Issue("DELEGATECALL to dynamic address", "Informational")

                issue.description = \
                    "The function " + call.node.function_name + " in contract '" + call.node.module_name + " delegates execution to a contract with a dynamic address." \
                    "To address:" + str(call.to)

                issues.append(issue)

    return issues
