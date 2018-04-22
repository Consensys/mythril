from z3 import *
from mythril.analysis.ops import *
from mythril.analysis.report import Issue
from mythril.analysis import solver
import re
import logging


'''
MODULE DESCRIPTION:

Check for call.value()() to external addresses
'''

MAX_SEARCH_DEPTH = 64


def search_children(statespace, node, start_index=0, depth=0, results=[]):

    logging.debug("SEARCHING NODE %d", node.uid)

    if(depth < MAX_SEARCH_DEPTH):

        nStates = len(node.states)

        if nStates > start_index:

            for j in range(start_index, nStates):
                if node.states[j].get_current_instruction()['opcode'] == 'SSTORE':
                    results.append(node.states[j].get_current_instruction()['address'])

        children = []

        for edge in statespace.edges:
            if edge.node_from == node.uid:
                children.append(statespace.nodes[edge.node_to])

        if (len(children)):
            for node in children:
                return search_children(statespace, node, depth=depth + 1, results=results)

    return results


calls_visited = []


def execute(statespace):

    issues = []

    for call in statespace.calls:

        state = call.state
        address = state.get_current_instruction()['address']

        if (call.type == "CALL"):

            logging.info("[EXTERNAL_CALLS] Call to: %s, value = %s, gas = %s" % (str(call.to), str(call.value), str(call.gas)))

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
                        idx = m.group(1)

                        func = statespace.find_storage_write(state.environment.active_account.address, idx)

                        if func:

                            description += \
                                "an address found at storage slot " + str(idx) + ". " + \
                                "This storage slot can be written to by calling the function `" + func + "`. "
                            user_supplied = True

                if user_supplied:

                    description += "Generally, it is not recommended to call user-supplied adresses using Solidity's call() construct. Note that attackers might leverage reentrancy attacks to exploit race conditions or manipulate this contract's state."

                    issue = Issue(call.node.contract_name, call.node.function_name, address, "Message call to external contract", "Warning", description)

                else:

                    description += "to another contract. Make sure that the called contract is trusted and does not execute user-supplied code."

                    issue = Issue(call.node.contract_name, call.node.function_name, address, "Message call to external contract", "Informational", description)

                issues.append(issue)

                if address not in calls_visited:
                    calls_visited.append(address)

                    logging.debug("[EXTERNAL_CALLS] Checking for state changes starting from " + call.node.function_name)

                    # Check for SSTORE in remaining instructions in current node & nodes down the CFG

                    state_change_addresses = search_children(statespace, call.node, call.state_index + 1, depth=0, results=[])

                    logging.debug("[EXTERNAL_CALLS] Detected state changes at addresses: " + str(state_change_addresses))

                    if (len(state_change_addresses)):
                        for address in state_change_addresses:
                            description = "The contract account state is changed after an external call. Consider that the called contract could re-enter the function before this state change takes place. This can lead to business logic vulnerabilities."
                            issue = Issue(call.node.contract_name, call.node.function_name, address, "State change after external call", "Warning", description)
                            issues.append(issue)

    return issues
