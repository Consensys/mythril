import logging
from z3 import BitVec, simplify
import mythril.laser.ethereum.util as util
from mythril.laser.ethereum.state import Account
from mythril.laser.ethereum.svm import CalldataType
import re

def get_call_parameters(global_state, dynamic_loader, with_value=False):
    state = global_state.mstate
    instr = global_state.get_current_instruction()

    if with_value:
        gas, to, value, meminstart, meminsz, memoutstart, memoutsz = \
            state.stack.pop(), state.stack.pop(), state.stack.pop(), state.stack.pop(), state.stack.pop(), state.stack.pop(), state.stack.pop()
    else:
        gas, to, meminstart, meminsz, memoutstart, memoutsz = \
            state.stack.pop(), state.stack.pop(), state.stack.pop(), state.stack.pop(), state.stack.pop(), state.stack.pop()
        value = None

    callee_address = get_callee_address(global_state, dynamic_loader)

    if int(callee_address, 16) < 5:
        logging.info("Native contract called: " + callee_address)
        # Todo: Implement native contracts
        global_state.mstate.stack.append(BitVec("retval_" + str(instr['address']), 256))
        return [global_state]

    callee_account = get_callee_account(global_state, callee_address, dynamic_loader)
    call_data, call_data_type = get_call_data(global_state, meminstart, meminsz)

    return callee_account, call_data, value, call_data_type, gas


def get_callee_address(global_state, dynamic_loader):
    to = global_state.mstate.stack[-2]
    environment = global_state.environment

    try:
        callee_address = hex(util.get_concrete_int(to))
        return callee_address
    except AttributeError:
        logging.info("Symbolic call encountered")

    match = re.search(r'storage_(\d+)', str(simplify(to)))
    logging.debug("CALL to: " + str(simplify(to)))

    if match is None or dynamic_loader is None:
        raise ValueError()

    index = int(match.group(1))
    logging.info("Dynamic contract address at storage index {}".format(index))

    # attempt to read the contract address from instance storage
    try:
        callee_address = dynamic_loader.read_storage(environment.active_account.address, index)
    except:
        logging.debug("Error accessing contract storage.")
        raise ValueError()

    # testrpc simply returns the address, geth response is more elaborate.
    if not re.match(r"^0x[0-9a-f]{40}$", callee_address):
        callee_address = "0x" + callee_address[26:]

    return callee_address


def get_callee_account(global_state, callee_address, dynamic_loader):
    environment = global_state.environment
    accounts = global_state.accounts

    try:
        return global_state.accounts[callee_address]
    except KeyError:
        # We have a valid call address, but contract is not in the modules list
        logging.info("Module with address " + callee_address + " not loaded.")

    if dynamic_loader is None:
        raise ValueError()

    logging.info("Attempting to load dependency")

    try:
        code = dynamic_loader.dynld(environment.active_account.address, callee_address)
    except Exception as e:
        logging.info("Unable to execute dynamic loader.")
        raise ValueError()
    if code is None:
        logging.info("No code returned, not a contract account?")
        raise ValueError()

    accounts[callee_address] = Account(callee_address, code, callee_address)

    logging.info("Dependency loaded: " + callee_address)


def get_call_data(global_state, meminstart, meminsz):
    state = global_state.mstate
    try:
        # TODO: This only allows for either fully concrete or fully symbolic calldata.
        # Improve management of memory and callata to support a mix between both types.
        call_data = state.memory[util.get_concrete_int(meminstart):util.get_concrete_int(meminstart + meminsz)]
        if len(call_data) < 32:
            call_data += [0] * (32 - len(call_data))
        call_data_type = CalldataType.CONCRETE
        logging.debug("Calldata: " + str(call_data))
    except AttributeError:
        logging.info("Unsupported symbolic calldata offset")
        call_data_type = CalldataType.SYMBOLIC
        call_data = []

    return call_data, call_data_type
