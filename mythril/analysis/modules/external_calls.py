from z3 import *
from mythril.analysis.ops import *
from mythril.analysis.report import Issue
import re
import logging


'''
MODULE DESCRIPTION:

Check for call.value()() to an untrusted address
'''


def execute(statespace):

    logging.debug("Executing module: EXTERNAL_CALLS")

    issues = []

    for call in statespace.calls:

        state = call.state
        address = state.get_current_instruction()['address']

        if (call.type == "CALL"):

            logging.debug("[EXTERNAL_CALLS] Call to: " + str(call.to) + ", value " + str(call.value) + ", gas = " + str(call.gas))

            if (call.to.type == VarType.SYMBOLIC and (call.gas.type == VarType.CONCRETE and call.gas.val > 2300) or (call.gas.type == VarType.SYMBOLIC and "2300" not in str(call.gas))):

                description = "This contract executes a message call to "

                target = str(call.to)
                user_supplied = False

                if ("calldata" in target or "caller" in target):

                    if ("calldata" in target):
                        description += "an address provided as a function argument. "
                    else:
                        description += "the address of the transaction sender. "

                    user_supplied = True
                else:
                    m = re.search(r'storage_([a-z0-9_&^]+)', str(call.to))

                    if (m):
                        index = m.group(1)

                        func = statespace.find_storage_write(index)

                        if func:

                            description += \
                                "an address found at storage slot " + str(index) + ". " + \
                                "This storage slot can be written to by calling the function '" + func + "'. "
                            user_supplied = True
                            break

                if user_supplied:

                    description += "Generally, it is not recommended to call user-supplied adresses using Solidity's call() construct. Note that attackers might leverage reentrancy attacks to exploit race conditions or manipulate this contract's state."

                    issue = Issue(call.node.contract_name, call.node.function_name, address, "Message call to external contract", "Warning", description)

                else:

                    description += "to another contract. Make sure that the called contract is trusted and does not execute user-supplied code."

                    issue = Issue(call.node.contract_name, call.node.function_name, address, "Message call to external contract", "Informational", description)

                issues.append(issue)

    return issues
