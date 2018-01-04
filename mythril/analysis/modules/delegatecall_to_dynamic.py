from z3 import *
from mythril.analysis.ops import *
from mythril.analysis.report import Issue
import re
import logging


'''
MODULE DESCRIPTION:

Check for invocations of delegatecall/callcode to a user-supplied address
'''

def execute(statespace):

    logging.debug("Executing module: DELEGATECALL_TO_DYNAMIC")

    issues = []

    for call in statespace.calls:

        if (call.type == "DELEGATECALL" or call.type == "CALLCODE"):

            if (call.to.type == VarType.SYMBOLIC):

                if ("calldata" in str(call.to)):
                    issue = Issue(call.node.module_name, call.node.function_name, call.addr, call.type + " to dynamic address")

                    issue.description = \
                        "The function " + call.node.function_name + " delegates execution to a contract address obtained from calldata.\n" \
                        "Recipient address: " + str(call.to)

                    issues.append(issue)
                else:
                    m = re.search(r'storage_([a-z0-9_&^]+)', str(call.to))

                    if (m):
                        index = m.group(1)
                        logging.debug("DELEGATECALL to contract address in storage")

                        try:

                            for s in statespace.sstors[index]:

                                if s.tainted:
                                    issue = Issue(call.type + " to dynamic address in storage", "Warning")
                                    issue.description = \
                                        "The function " + call.node.function_name + " in contract '" + call.node.module_name + " delegates execution to a contract address stored in a state variable. " \
                                        "There is a check on storage index " + str(index) + ". This storage index can be written to by calling the function '" + s.node.function_name + "'.\n" \
                                        "Make sure that the contract address cannot be set by untrusted users."
                                    issues.append(issue)
                                    break

                        except KeyError:
                            logging.debug("[ETHER_SEND] No storage writes to index " + str(index))

                    else:

                        issue = Issue(call.node.module_name, call.node.function_name, call.addr, "DELEGATECALL to dynamic address", "Informational")

                        issue.description = \
                            "The function " + call.node.function_name + " in contract '" + call.node.module_name + " delegates execution to a contract with a dynamic address." \
                            "To address:" + str(call.to)

                        issues.append(issue)

    return issues
