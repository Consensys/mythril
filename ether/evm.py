from ethereum import vm, messages, transactions
from ethereum.state import State
from ethereum.slogging import get_logger
from logging import StreamHandler
from io import StringIO
import codecs
from .util import safe_decode


def trace(code, address = "", calldata = ""):

	logHandlers = ['eth.vm.op', 'eth.vm.op.stack', 'eth.vm.op.memory', 'eth.vm.op.storage']

	output = StringIO()
	streamHandler = StreamHandler(output)

	for handler in logHandlers:
		log_vm_op = get_logger(handler)
		log_vm_op.setLevel("TRACE")
		log_vm_op.addHandler(streamHandler)

	addr_from = codecs.decode('0123456789ABCDEF0123456789ABCDEF01234567', 'hex_codec')
	addr_to = safe_decode(address)

	state = State()

	ext = messages.VMExt(state, transactions.Transaction(0, 0, 21000, addr_from, 0, addr_to))

	message = vm.Message(addr_from, addr_to, 0, 21000, calldata, code_address=addr_to)

	res, gas, dat = vm.vm_execute(ext, message, code)

	streamHandler.flush()

	# print(output.getvalue())

	ret = output.getvalue()

	return ret