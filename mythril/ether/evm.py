from ethereum import vm, messages, transactions
from ethereum.state import State
from ethereum.slogging import get_logger
from mythril.ether import util
from logging import StreamHandler
from io import StringIO
import re


def trace(code, calldata=""):
    log_handlers = ['eth.vm.op', 'eth.vm.op.stack', 'eth.vm.op.memory', 'eth.vm.op.storage']

    output = StringIO()
    stream_handler = StreamHandler(output)

    for handler in log_handlers:
        log_vm_op = get_logger(handler)
        log_vm_op.setLevel("TRACE")
        log_vm_op.addHandler(stream_handler)

    addr = bytes.fromhex('0123456789ABCDEF0123456789ABCDEF01234567')

    state = State()

    ext = messages.VMExt(state, transactions.Transaction(0, 0, 21000, addr, 0, addr))

    message = vm.Message(addr, addr, 0, 21000, calldata)

    vm.vm_execute(ext, message, util.safe_decode(code))

    stream_handler.flush()

    ret = output.getvalue()

    lines = ret.split("\n")

    trace = []

    for line in lines:

        m = re.search(r'pc=b\'(\d+)\'.*op=([A-Z0-9]+)', line)

        if m:
            pc = m.group(1)
            op = m.group(2)

            m = re.match(r'.*stack=(\[.*?\])', line)

            if (m):

                stackitems = re.findall(r'b\'(\d+)\'', m.group(1))

                stack = "[";

                if len(stackitems):

                    for i in range(0, len(stackitems) - 1):
                        stack += hex(int(stackitems[i])) + ", "

                    stack += hex(int(stackitems[-1]))

                stack += "]"

            else:
                stack = "[]"

            if re.match(r'^PUSH.*', op):
                val = re.search(r'pushvalue=(\d+)', line).group(1)
                pushvalue = hex(int(val))
                trace.append({'pc': pc, 'op': op, 'stack': stack, 'pushvalue': pushvalue})
            else:
                trace.append({'pc': pc, 'op': op, 'stack': stack})

    return trace
