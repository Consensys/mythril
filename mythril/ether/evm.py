from ethereum import vm, messages, transactions
from ethereum.state import State
from ethereum.slogging import get_logger
from mythril.ether import util
from logging import StreamHandler
from io import StringIO
import codecs


def trace(code, calldata = ""):

	logHandlers = ['eth.vm.op', 'eth.vm.op.stack', 'eth.vm.op.memory', 'eth.vm.op.storage']

	output = StringIO()
	streamHandler = StreamHandler(output)

	for handler in logHandlers:
		log_vm_op = get_logger(handler)
		log_vm_op.setLevel("TRACE")
		log_vm_op.addHandler(streamHandler)

	addr = codecs.decode('0123456789ABCDEF0123456789ABCDEF01234567', 'hex_codec')

	state = State()

	ext = messages.VMExt(state, transactions.Transaction(0, 0, 21000, addr, 0, addr))

	message = vm.Message(addr, addr, 0, 21000, calldata)

	res, gas, dat = vm.vm_execute(ext, message, util.safe_decode(code))

	streamHandler.flush()

	ret = output.getvalue()

	return ret