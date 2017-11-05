from z3 import *
from laser.ethereum import helper
import re
import logging
from enum import Enum


class TransferType(Enum):
    HARDCODED = 1
    CALLDATA = 2
    CALLER = 3
    OTHER = 3


def execute(statespace):

    for call in statespace.calls:

        if str(call.node.function_name) == 'execute(address,uint256,bytes)':

            print(str(call.node.module_name) + ":" + str(call.node.function_name) + ": " + str(call.call_type) + " " + str(call.to) + " value " + str(call.call_value))

            s = Solver()

            s.set(timeout=5000)



            print("--- CONSTRAINTS ---")
            for constraint in call.node.constraints:
                s.add(constraint)
                print(simplify(constraint))

            print("--- SOLUTION ---")

            if (s.check() == sat):

                m = s.model()

                for d in m.decls():
                    print("%s = 0x%x" % (d.name(), m[d].as_long()))

            else:
                print("unsat")  


            # print("CONSTRAINTS")

            # print(str(call.node.constraints))


            '''
            node = svm.nodes[k]

            for instruction in node.instruction_list:

                if(instruction['opcode'] == "CALL"):

                    state = node.states[instruction['address']]

                    gas, to, value, meminstart, meminsz, memoutstart, memoutsz = \
                            state.stack.pop(), state.stack.pop(), state.stack.pop(), state.stack.pop(), state.stack.pop(), state.stack.pop(), state.stack.pop()

                    interesting = False

                    try:
                        value = helper.get_concrete_int(value)
                        if(value > 0):
                            print ("Call with non-zero value: " + str(value))
                            interesting = True
                    except AttributeError:
                        print ("Call with symbolic value: " + str(value))
                        interesting = True

                    if interesting:

                        try:
                            to = helper.get_concrete_int(to).hex()
                        except AttributeError:
                            to = str(simplify(to))

                        print("Function name: " + str(node.function_name))

                        m = re.search(r'calldata_(\d)', to)

                        if m:
                            cd_index = m.group(1)
                            print("Transfer to [calldata_" + str(cd_index) + "] " + str(node.function_name))
                            transfer_type = TransferType.CALLDATA
                        else:
                            m = re.search(r'caller', to)

                            if m:
                                print("Transfer to msg.sender")
                                transfer_type = TransferType.CALLER
                            else:
                                m = re.match(r'0x[0-9a-f]+', to)
                                if m:
                                    print("Transfer to address " + to)
                                    transfer_type = TransferType.HARDCODED
                                else:
                                    print("Transfer to " + to)
                                    transfer_type = TransferType.OTHER


                        for constraint in node.constraints:
                            m = re.search(r'caller', str(constraint))
                            n = re.search(r'storage_(\d+)', str(constraint))

                            if (m and n):
                                storage_index = n.group(1)

                                print("constraint on caller == storage_" + str(storage_index))
                                break

                        s = Solver()

                        s.set(timeout=5000)

                        for constraint in node.constraints:
                            s.add(constraint)

                        if (s.check() == sat):

                            m = s.model()

                            for d in m.decls():
                                print("%s = 0x%x" % (d.name(), m[d].as_long()))

                        else:
                            print("unsat")
            '''