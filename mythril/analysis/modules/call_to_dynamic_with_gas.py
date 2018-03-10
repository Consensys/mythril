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

    logging.debug("Executing module: CALL_TO_DYNAMIC_WITH_GAS")

    issues = []

    for call in statespace.calls:

        state = call.state
        address = state.get_current_instruction()['address']

        if (call.type == "CALL"):

            logging.debug("[CALL_TO_DYNAMIC_WITH_GAS] Call to: " + str(call.to) + ", value " + str(call.value) + ", gas = " + str(call.gas))

            if (call.to.type == VarType.SYMBOLIC and (call.gas.type == VarType.CONCRETE and call.gas.val > 2300) or (call.gas.type == VarType.SYMBOLIC and "2300" not in str(call.gas))):

                description = "The function " + call.node.function_name + " contains a function call to "

                target = str(call.to)
                is_valid = False

                if ("calldata" in target or "caller" in target):

                    if ("calldata" in target):
                        description += "an address provided as a function argument."
                    else:
                        description += "the address of the transaction sender."

                    is_valid = True
                else:
                    m = re.search(r'storage_([a-z0-9_&^]+)', str(call.to))

                    if (m):
                        index = m.group(1)

                        func = statespace.find_storage_write(index)

                        if func:

                            description += \
                                "an address found at storage position " + str(index) + ".\n" + \
                                "This storage position can be written to by calling the function '" + func + "'.\n" \
                                "Verify that the contract address cannot be set by untrusted users.\n"

                            is_valid = True
                            break

                if is_valid:

                    description += "The available gas is forwarded to the called contract. Make sure that the logic of the calling contract is not adversely affected if the called contract misbehaves (e.g. reentrancy)."

                    issue = Issue(call.node.contract_name, call.node.function_name, address, "Message call to external contract", "Warning", description)

                    issues.append(issue)

    return issues
