from ethereum import vm, messages, transactions
from ethereum.state import State
from ethereum.slogging import get_logger
from logging import StreamHandler
import sys
import codecs


def trace(code):

	logHandlers = ['eth.vm.op', 'eth.vm.op.stack', 'eth.vm.op.memory', 'eth.vm.op.storage']

	streamHandler = StreamHandler(sys.stdout)

	for handler in logHandlers:
		log_vm_op = get_logger(handler)
		log_vm_op.setLevel("TRACE")
		log_vm_op.addHandler(streamHandler)

	addr = codecs.decode('0123456789ABCDEF0123456789ABCDEF01234567', 'hex_codec')

	state = State()

	ext = messages.VMExt(state, transactions.Transaction(0, 0, 21000, addr, 0, addr))

	msg = vm.Message(addr, addr)

	vm.vm_execute(ext, msg, code)