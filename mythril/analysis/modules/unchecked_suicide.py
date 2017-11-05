from z3 import *
from mythril.analysis.ops import *
from mythril.analysis.report import Issue


'''
MODULE DESCRIPTION:

Check for SUICIDE instructions that are not constrained by caller.
'''

def execute(statespace):

    issues = []

    svm = statespace.svm

    for k in svm.nodes:
        node = svm.nodes[k]

        for instruction in node.instruction_list:

            if(instruction['opcode'] == "SUICIDE"):

                state = node.states[instruction['address']]
                to = state.stack.pop()

                constraint_on_caller = False

                for constraint in node.constraints:
                    if "caller" in str(constraint):
                        constraint_on_caller = True
                        break

                if not constraint_on_caller:
                    s = Solver()

                    if (s.check() == sat):
                        issue = Issue("Unchecked SUICIDE", "VULNERABILITY")
                        issue.description = "The function " + node.function_name + " calls the SUICIDE instruction. It appears as if the function does not verify the caller address.\n"

                        if ("caller" in str(to)):
                            issue.description += "The remaining Ether is sent to the caller's address.\n"
                        elif ("storage" in str(to)):
                            issue.description += "The remaining Ether is sent to a stored address\n"
                        else:
                            issue.description += "The remaining Ether is sent to: " + str(to) + "\n"

                        issue.description += "Solver output:\n"

                        m = s.model()

                        for d in m.decls():
                            issue.description += "%s = 0x%x\n" % (d.name(), m[d].as_long())

                        issues.append(issue)    

    return issues



