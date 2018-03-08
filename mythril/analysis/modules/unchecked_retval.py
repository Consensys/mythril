from z3 import *
import re
from mythril.analysis.ops import *
from mythril.analysis.report import Issue
import logging
from laser.ethereum import helper


'''
MODULE DESCRIPTION:

Test whether CALL return value is checked.

For direct calls, the Solidity compiler auto-generates this check. E.g.:

    Alice c = Alice(address);
    c.ping(42);

Here the CALL will be followed by IZSERO(retval), if retval = ZERO then state is reverted.

For low-level-calls this check is omitted. E.g.:

    c.call.value(0)(bytes4(sha3("ping(uint256)")),1);

'''


def execute(statespace):

    logging.debug("Executing module: UNCHECKED_RETVAL")

    issues = []
    visited = []

    for call in statespace.calls:

        state = call.state
        address = state.get_current_instruction()['address']

        # Only needs to be checked once per call instructions (it's essentially just static analysis)

        if call.state.mstate.pc in visited:
            continue
        else:
            visited.append(call.state.mstate.pc)

        retval_checked = False

        # ISZERO retval is expected to be found within the next few instructions.

        for i in range(0, 10):

            _state = call.node.states[call.state_index + i]

            try:
                instr = _state.get_current_instruction()
            except IndexError:
                break

            if (instr['opcode'] == 'ISZERO' and re.search(r'retval', str(_state.mstate.stack[-1]))):
                retval_checked = True
                break

        if not retval_checked:

            issue = Issue(call.node.contract_name, call.node.function_name, address, "Unchecked CALL return value")

            if (call.to.type == VarType.CONCRETE):
                receiver = hex(call.to.val)
            elif (re.search(r"caller", str(call.to))):
                receiver = "msg.sender"
            elif (re.search(r"storage", str(call.to))):
                receiver = "an address obtained from storage"
            else:
                receiver = str(call.to)


            issue.description = \
                "The function " + call.node.function_name + " contains a call to " + receiver + ".\n" \
                "The return value of this call is not checked. Note that the function will continue to execute with a return value of '0' if the called contract throws."

            issues.append(issue)

    return issues