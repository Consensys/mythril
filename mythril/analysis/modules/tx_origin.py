from mythril.analysis.report import Issue
import re


'''
MODULE DESCRIPTION:

Check for constraints on tx.origin (i.e., access to some functionality is restricted to a specific origin).
'''

def execute(statespace):

    issues = []

    for k in statespace.nodes:
        node = statespace.nodes[k]

        for constraint in node.constraints:

            if(re.search(r'origin', str(constraint))):

                issue = Issue(node.module_name, node.function_name, None,  "Use of tx.origin", "Warning", \
                    "Access to the function " + node.function_name + " is granted based on tx.origin. Use tx.sender instead.\nSee also: https://solidity.readthedocs.io/en/develop/security-considerations.html#tx-origin"
                )
                
                issues.append(issue)
    
    return issues
