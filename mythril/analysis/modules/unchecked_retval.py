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

        next_i = helper.get_instruction_index(call.node.instruction_list, call.addr) + 1

        instr = call.node.instruction_list[next_i]
 
        logging.info("CALL. Next instruction: " + instr['opcode'])

        # The stack contents at a particular point of execution are found in node.states[address].stack

        if (instr['opcode'] != 'ISZERO' or not re.search(r'retval', str(call.node.states[call.addr + 1].stack[-1]))):

            issue = Issue("Unchecked CALL return value")
            issue.description = \
                "The function " + call.node.function_name + " in contract '" + call.node.module_name + "' contains a call to " + str(call.to) + ".\n" \
                "The return value of this call is not checked. Note that the function will continue to execute even if the called contract throws."

            issues.append(issue)

    return issues