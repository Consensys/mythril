from ethereum import vm, messages, transactions
from ethereum.state import State
from ethereum.slogging import get_logger
from logging import StreamHandler
import sys
import codecs
from .util import safe_decode


def trace(code, address = "", calldata = ""):

	logHandlers = ['eth.vm.op', 'eth.vm.op.stack', 'eth.vm.op.memory', 'eth.vm.op.storage']

	streamHandler = StreamHandler(sys.stdout)

	for handler in logHandlers:
		log_vm_op = get_logger(handler)
		log_vm_op.setLevel("TRACE")
		log_vm_op.addHandler(streamHandler)

	addr_from = codecs.decode('0123456789ABCDEF0123456789ABCDEF01234567', 'hex_codec')
	addr_to = safe_decode(address)
	data = safe_decode(calldata)

	state = State()

	ext = messages.VMExt(state, transactions.Transaction(0, 0, 21000, addr_from, 0, addr_to))

	message = vm.Message(addr_from, addr_to, 0, 21000, data, code_address=addr_to)

	res, gas, dat = vm.vm_execute(ext, message, code)