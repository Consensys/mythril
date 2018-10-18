import re
from z3 import *
from mythril.analysis.ops import VarType
from mythril.analysis import solver
from mythril.analysis.report import Issue
from mythril.analysis.swc_data import TIMESTAMP_DEPENDENCE, PREDICTABLE_VARS_DEPENDENCE
from mythril.exceptions import UnsatError
import logging

'''
MODULE DESCRIPTION:

Check for CALLs that send >0 Ether as a result of computation based on predictable variables such as
block.coinbase, block.gaslimit, block.timestamp, block.number

TODO:
- block.blockhash(block.number-1)
- block.blockhash(some_block_past_256_blocks_from_now)==0
- external source of random numbers (e.g. Oraclize)
'''


def execute(statespace):

    logging.debug("Executing module: DEPENDENCE_ON_PREDICTABLE_VARS")

    issues = []

    for call in statespace.calls:

        if "callvalue" in str(call.value):
            logging.debug("[DEPENDENCE_ON_PREDICTABLE_VARS] Skipping refund function")
            continue

        # We're only interested in calls that send Ether

        if call.value.type == VarType.CONCRETE and call.value.val == 0:
            continue

        address = call.state.get_current_instruction()['address']

        description = "In the function `" + call.node.function_name + "` "
        description += "the following predictable state variables are used to determine Ether recipient:\n"

        # First check: look for predictable state variables in node & call recipient constraints

        vars = ["coinbase", "gaslimit", "timestamp", "number"]

        found = []
        for var in vars:
            for constraint in call.node.constraints + [call.to]:
                if var in str(constraint):
                    found.append(var)

        if len(found):
            for item in found:
                description += "- block.{}\n".format(item)
            if solve(call):
                swc_type = TIMESTAMP_DEPENDENCE if item == 'timestamp' else PREDICTABLE_VARS_DEPENDENCE
                issue = Issue(contract=call.node.contract_name, function=call.node.function_name, address=address,
                              swc_id=swc_type, title="Dependence on predictable environment variable",
                              _type="Warning", description=description)
                issues.append(issue)

        # Second check: blockhash

        for constraint in call.node.constraints + [call.to]:
            if "blockhash" in str(constraint):
                description = "In the function `" + call.node.function_name + "` "
                if "number" in str(constraint):
                    m = re.search(r'blockhash\w+(\s-\s(\d+))*', str(constraint))
                    if m and solve(call):

                        found = m.group(1)

                        if found:  # block.blockhash(block.number - N)
                            description += "predictable expression 'block.blockhash(block.number - " + m.group(2) + \
                                ")' is used to determine Ether recipient"
                            if int(m.group(2)) > 255:
                                description += ", this expression will always be equal to zero."
                        elif "storage" in str(constraint):  # block.blockhash(block.number - storage_0)
                            description += "predictable expression 'block.blockhash(block.number - " + \
                                           "some_storage_var)' is used to determine Ether recipient"
                        else:  # block.blockhash(block.number)
                            description += "predictable expression 'block.blockhash(block.number)'" + \
                                           " is used to determine Ether recipient"
                            description += ", this expression will always be equal to zero."

                        issue = Issue(contract=call.node.contract_name, function=call.node.function_name,
                                      address=address, title="Dependence on predictable variable",
                                      _type="Warning", description=description, swc_id=PREDICTABLE_VARS_DEPENDENCE)
                        issues.append(issue)
                        break
                else:
                    r = re.search(r'storage_([a-z0-9_&^]+)', str(constraint))
                    if r:  # block.blockhash(storage_0)

                        '''
                        We actually can do better here by adding a constraint blockhash_block_storage_0 == 0
                        and checking model satisfiability. When this is done, severity can be raised
                        from 'Informational' to 'Warning'.
                        Checking that storage at given index can be tainted is not necessary, since it usually contains
                        block.number of the 'commit' transaction in commit-reveal workflow.
                        '''

                        index = r.group(1)
                        if index and solve(call):
                            description += 'block.blockhash() is calculated using a value from storage ' \
                                           'at index {}'.format(index)
                            issue = Issue(contract=call.node.contract_name, function=call.node.function_name,
                                          address=address, title="Dependence on predictable variable",
                                          _type="Informational", description=description, swc_id=PREDICTABLE_VARS_DEPENDENCE)
                            issues.append(issue)
                            break
    return issues


def solve(call):
    try:
        model = solver.get_model(call.node.constraints)
        logging.debug("[DEPENDENCE_ON_PREDICTABLE_VARS] MODEL: " + str(model))

        for decl in model.decls():
            logging.debug("[DEPENDENCE_ON_PREDICTABLE_VARS] main model: %s = 0x%x" % (decl.name(), model[decl].as_long()))
        return True

    except UnsatError:
        logging.debug("[DEPENDENCE_ON_PREDICTABLE_VARS] no model found")
        return False
