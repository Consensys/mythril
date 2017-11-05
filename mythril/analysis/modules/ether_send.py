from z3 import *
import re
import logging
from enum import Enum
from mythril.analysis.ops import *


class InputSource(Enum):
    CALLDATA = 1
    STORAGE = 2


def execute(statespace):

    for call in statespace.calls:

        logging.info("CALL: " + str(call.node.module_name) + ":" + str(call.node.function_name) + ": " + str(call.type) + " " + str(call.to) + " value " + str(call.value))

        interesting = False

        if (call.value.type == VarType.CONCRETE and call.value.val > 0) or (call.value.type == VarType.SYMBOLIC):

            logging.info("CALL with non-zero value: " + str(call.node.module_name) + ":" + str(call.node.function_name) + ": " + str(call.type) + " " + str(call.to) + " value " + str(call.value))

            interesting = True

            if call.to.type == VarType.CONCRETE:
                logging.info("Concrete 'to' address: " + call.to.hex())
            else:
                m = re.search(r"calldata", str(call.to))

                if (m):
                    logging.info("To-address from calldata: " + str(call.to))

            if call.value.type == VarType.CONCRETE:
                logging.info("Sending concrete amount: " + call.value)
            else:
                m = re.search(r"calldata", str(call.to))

                if (m):
                    logging.info("To-address from calldata: " + str(call.to))


        if (interesting):

            s = Solver()
            s.set(timeout=10000)

            for constraint in call.node.constraints:
                s.add(constraint)

            logging.info("SOLUTION:")

            if (s.check() == sat):

                m = s.model()

                for d in m.decls():
                    logging.info("%s = 0x%x" % (d.name(), m[d].as_long()))

            else:
                logging.info("unsat")
