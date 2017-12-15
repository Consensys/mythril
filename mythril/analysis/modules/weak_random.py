from z3 import *
from mythril.analysis.ops import *
from mythril.analysis import solver
from mythril.analysis.report import Issue
from mythril.exceptions import UnsatError
import logging

'''
MODULE DESCRIPTION:

Check for CALLs that send >0 Ether as a result of computation based on predictable state variables such as 
block.coinbase, block.gaslimit, block.timestamp, block.number

TODO:
- block.blockhash(block.number-1)
- block.blockhash(some_block_past_256_blocks_from_now)==0
- external source of random numbers (e.g. Oraclize)
'''


def execute(statespace):
    issues = []

    for call in statespace.calls:

        if ("callvalue" in str(call.value)):
            logging.debug("[WEAK_RANDOM] Skipping refund function")
            continue

        # We're only interested in calls that send Ether

        if call.value.type == VarType.CONCRETE:
            if call.value.val == 0:
                continue



        description  = "In the function '" + call.node.function_name + "' "
        description += "the following predictable state variables are used to determine Ether recipient:\n"

        # Look for predictable state variables in node & call recipient constraints

        vars = ["coinbase", "gaslimit", "timestamp", "number"]

        found = []
        for var in vars:
            for constraint in call.node.constraints:
                if var in str(constraint):
                    found.append(var)
                    break
            else:
                if var in str(call.to):
                    found.append(var)

        if len(found):
            for item in found:
                description += "- block.{}\n".format(item)
            try:
                model = solver.get_model(call.node.constraints)
                logging.debug("[WEAK_RANDOM] MODEL: " + str(model))

                for d in model.decls():
                    logging.debug("[WEAK_RANDOM] main model: %s = 0x%x" % (d.name(), model[d].as_long()))

                issue = Issue(call.node.module_name, call.node.function_name, call.addr, "Weak random", "Warning",
                              description)
                issues.append(issue)

            except UnsatError:
                logging.debug("[WEAK_RANDOM] no model found")

    return issues
