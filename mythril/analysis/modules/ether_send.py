from z3 import *
from laser.ethereum import helper
import re
import logging
from enum import Enum
from mythril.analysis.ops import *


class TransferType(Enum):
    HARDCODED = 1
    CALLDATA = 2
    CALLER = 3
    OTHER = 3


def execute(statespace):

    for call in statespace.calls:

        # print(str(call.node.module_name) + ":" + str(call.node.function_name) + ": " + str(call.call_type) + " " + str(call.to) + " value " + str(call.call_value))

        # Checks on value

        interesting = False

        if (call.call_value.type == VarType.CONCRETE and call.call_value.val > 0):
            interesting = True

        if (call.call_value.type == VarType.SYMBOLIC):
            interesting = True            

        if (interesting):

            print(str(call.node.module_name) + ":" + str(call.node.function_name) + ": " + str(call.call_type) + " " + str(call.to) + " value " + str(call.call_value))

            s = Solver()
            s.set(timeout=10000)

            for constraint in call.node.constraints:
                s.add(constraint)

            print("SOLUTION:")

            if (s.check() == sat):

                m = s.model()

                for d in m.decls():
                    print("%s = 0x%x" % (d.name(), m[d].as_long()))

            else:
                print("unsat")  
