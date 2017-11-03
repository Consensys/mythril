from z3 import *


def execute(svm):

    for k in svm.nodes:
        node = svm.nodes[k]

        for instruction in node.instruction_list:

            if(instruction['opcode'] == "SUICIDE"):
                state = node.states[instruction['address']]
                to = state.stack.pop()

                print("SUICIDE to: " + str(to))
                print("function: " + str(node.function_name))

                s = Solver()

                for constraint in node.constraints:
                    s.add(constraint)

                if (s.check() == sat):
                    print("MODEL:")

                    m = s.model()

                    for d in m.decls():
                        print("%s = 0x%x" % (d.name(), m[d].as_long()))
                else:
                    print("unsat")