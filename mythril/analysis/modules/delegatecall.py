import re
from mythril.analysis.ops import get_variable, VarType
from mythril.analysis.report import Issue
import logging


'''
MODULE DESCRIPTION:

Check for invocations of delegatecall(msg.data) in the fallback function.
'''


def execute(statespace):
    """
    Executes analysis module for delegate call analysis module
    :param statespace: Statespace to analyse
    :return: Found issues
    """
    issues = []

    for call in statespace.calls:

        if call.type is not "DELEGATECALL":
            continue
        if call.node.function_name is not "fallback":
            continue

        state = call.state
        address = state.get_current_instruction()['address']
        meminstart = get_variable(state.mstate.stack[-3])

        if meminstart.type == VarType.CONCRETE:
            issues += _concrete_call(call, state, address, meminstart)

        if call.to.type == VarType.SYMBOLIC:
            issues += _symbolic_call(call, state, address, statespace)

    return issues


def _concrete_call(call, state, address, meminstart):
    if not re.search(r'calldata.*_0', str(state.mstate.memory[meminstart.val])):
        return []

    issue = Issue(call.node.contract_name, call.node.function_name, address,
                  "Call data forwarded with delegatecall()", "Informational")

    issue.description = \
        "This contract forwards its call data via DELEGATECALL in its fallback function. " \
        "This means that any function in the called contract can be executed. Note that the callee contract will have " \
        "access to the storage of the calling contract.\n "

    target = hex(call.to.val) if call.to.type == VarType.CONCRETE else str(call.to)
    issue.description += "DELEGATECALL target: {}".format(target)

    return [issue]


def _symbolic_call(call, state, address, statespace):
    issue = Issue(call.node.contract_name, call.node.function_name, address, call.type + " to a user-supplied address")

    if "calldata" in str(call.to):

        issue.description = \
            "This contract delegates execution to a contract address obtained from calldata. "
        # TODO: this issue is never returned
        return []
    else:
        m = re.search(r'storage_([a-z0-9_&^]+)', str(call.to))

        if m:
            idx = m.group(1)

        func = statespace.find_storage_write(state.environment.active_account.address, idx)

        if (func):
            issue.description = "This contract delegates execution to a contract address in storage slot " + str(
                idx) + ". This storage slot can be written to by calling the function `" + func + "`. "

        else:
            logging.debug("[DELEGATECALL] No storage writes to index " + str(idx))

        issue.description += "Be aware that the called contract gets unrestricted access to this contract's state."
        return [issue]
