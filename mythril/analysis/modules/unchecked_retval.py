from z3 import *
import re
from mythril.analysis.report import Issue
import logging
from laser.ethereum import helper

'''
MODULE DESCRIPTION:

Test whether CALL return value is checked.

For direct calls, the Solidity compiler auto-generates this check. E.g.:

    Alice c = Alice(address);  
    c.ping(42);

Here the CALL will be followed by IZSERO(retval).

For low-level-calls this check is ommited. E.g.:

    c.call.value(0)(bytes4(sha3("ping(uint256)")),1);

'''

def execute(statespace):

    issues = []

    for call in statespace.calls:

        # The instructions executed in each node (basic block) are saved in node.instruction_list, e.g.:
        # [{address: "132", opcode: "CALL"}, {address: "133", opcode: "ISZERO"}]

        start_index = helper.get_instruction_index(call.node.instruction_list, call.addr) + 1
 
        retval_checked = False

        # ISZERO retval should be found within the next 10 instructions.
        # The stack contents at a particular point of execution are found in node.states[address].stack

        for i in range(0, 10):

            try:
                instr = call.node.instruction_list[start_index + i]
            except IndexError:
                break

            if (instr['opcode'] == 'ISZERO' and re.search(r'retval', str(call.node.states[instr['address']].stack[-1]))):
                retval_checked = True
                break

        if not retval_checked:

            issue = Issue("Unchecked CALL return value")

            if (re.search(r"caller", str(call.to))):
                receiver = "msg.sender"
            elif (re.search(r"storage", str(call.to))):
                receiver = "an address obtained from storage"
            else:
                receiver = str(call_to)


            issue.description = \
                "The function " + call.node.function_name + " in contract '" + call.node.module_name + "' contains a call to " + receiver + ".\n" \
                "The return value of this call is not checked. Note that the function will continue to execute with a return value of '0' if the called contract throws."

            issues.append(issue)

    return issues