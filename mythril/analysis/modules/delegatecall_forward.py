from z3 import *
import re
from mythril.analysis.ops import *
from mythril.analysis.report import Issue
import logging


'''
MODULE DESCRIPTION:

Check for invocations of delegatecall(msg.data) in the fallback function.
'''


def execute(statespace):

    logging.debug("Executing module: DELEGATECALL_FORWARD")

    issues = []
    visited = []

    for call in statespace.calls:

        state = call.state
        address = state.get_current_instruction()['address']

        # Only needs to be checked once per call instructions (essentially just static analysis)

        if address in visited:
            continue
        else:
            visited.append(address)

        if (call.type == "DELEGATECALL") and (call.node.function_name == "fallback"):

            stack = call.state.mstate.stack

            meminstart = get_variable(stack[-3])

            if meminstart.type == VarType.CONCRETE:

                if (re.search(r'calldata.*_0', str(state.mstate.memory[meminstart.val]))):

                    issue = Issue(call.node.contract_name, call.node.function_name, address, "CALLDATA forwarded with delegatecall()", "Informational")

                    issue.description = \
                        "This contract forwards its calldata via DELEGATECALL in its fallback function. " \
                        "This means that any function in the called contract can be executed. Note that the callee contract will have access to the storage of the calling contract.\n"   

                    if (call.to.type == VarType.CONCRETE):
                        issue.description += ("DELEGATECALL target: " + hex(call.to.val))
                    else:
                        issue.description += "DELEGATECALL target: " + str(call.to)

                    issues.append(issue)

    return issues
