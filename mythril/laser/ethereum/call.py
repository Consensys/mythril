"""This module contains the business logic used by Instruction in
instructions.py to get the necessary elements from the stack and determine the
parameters for the new global state."""

import logging
from typing import Union, List

from mythril.laser.ethereum import natives
from mythril.laser.ethereum.gas import OPCODE_GAS
from mythril.laser.smt import simplify, Expression, symbol_factory
import mythril.laser.ethereum.util as util
from mythril.laser.ethereum.state.account import Account
from mythril.laser.ethereum.state.calldata import (
    CalldataType,
    SymbolicCalldata,
    ConcreteCalldata,
    BaseCalldata,
)
from mythril.laser.ethereum.state.global_state import GlobalState
from mythril.support.loader import DynLoader
import re

"""
This module contains the business logic used by Instruction in instructions.py
to get the necessary elements from the stack and determine the parameters for the new global state.
"""

log = logging.getLogger(__name__)


def get_call_parameters(
    global_state: GlobalState, dynamic_loader: DynLoader, with_value=False
):
    """Gets call parameters from global state Pops the values from the stack
    and determines output parameters.

    :param global_state: state to look in
    :param dynamic_loader: dynamic loader to use
    :param with_value: whether to pop the value argument from the stack
    :return: callee_account, call_data, value, call_data_type, gas
    """
    gas, to = global_state.mstate.pop(2)
    value = global_state.mstate.pop() if with_value else 0
    memory_input_offset, memory_input_size, memory_out_offset, memory_out_size = global_state.mstate.pop(
        4
    )

    callee_address = get_callee_address(global_state, dynamic_loader, to)

    callee_account = None
    call_data, call_data_type = get_call_data(
        global_state, memory_input_offset, memory_input_size
    )

    if int(callee_address, 16) >= 5 or int(callee_address, 16) == 0:
        callee_account = get_callee_account(
            global_state, callee_address, dynamic_loader
        )

    return (
        callee_address,
        callee_account,
        call_data,
        value,
        call_data_type,
        gas,
        memory_out_offset,
        memory_out_size,
    )


def get_callee_address(
    global_state: GlobalState,
    dynamic_loader: DynLoader,
    symbolic_to_address: Expression,
):
    """Gets the address of the callee.

    :param global_state: state to look in
    :param dynamic_loader:  dynamic loader to use
    :param symbolic_to_address: The (symbolic) callee address
    :return: Address of the callee
    """
    environment = global_state.environment

    try:
        callee_address = hex(util.get_concrete_int(symbolic_to_address))
    except TypeError:
        log.debug("Symbolic call encountered")

        match = re.search(r"storage_(\d+)", str(simplify(symbolic_to_address)))
        log.debug("CALL to: " + str(simplify(symbolic_to_address)))

        if match is None or dynamic_loader is None:
            raise ValueError()

        index = int(match.group(1))
        log.debug("Dynamic contract address at storage index {}".format(index))

        # attempt to read the contract address from instance storage
        try:
            callee_address = dynamic_loader.read_storage(
                environment.active_account.address, index
            )
        # TODO: verify whether this happens or not
        except:
            log.debug("Error accessing contract storage.")
            raise ValueError

        # testrpc simply returns the address, geth response is more elaborate.
        if not re.match(r"^0x[0-9a-f]{40}$", callee_address):
            callee_address = "0x" + callee_address[26:]

    return callee_address


def get_callee_account(
    global_state: GlobalState, callee_address: str, dynamic_loader: DynLoader
):
    """Gets the callees account from the global_state.

    :param global_state: state to look in
    :param callee_address: address of the callee
    :param dynamic_loader: dynamic loader to use
    :return: Account belonging to callee
    """
    environment = global_state.environment
    accounts = global_state.accounts

    try:
        return global_state.accounts[callee_address]
    except KeyError:
        # We have a valid call address, but contract is not in the modules list
        log.debug("Module with address " + callee_address + " not loaded.")

    if dynamic_loader is None:
        raise ValueError()

    log.debug("Attempting to load dependency")

    try:
        code = dynamic_loader.dynld(environment.active_account.address, callee_address)
    except ValueError as error:
        log.debug("Unable to execute dynamic loader because: {}".format(str(error)))
        raise error
    if code is None:
        log.debug("No code returned, not a contract account?")
        raise ValueError()
    log.debug("Dependency loaded: " + callee_address)

    callee_account = Account(
        callee_address, code, callee_address, dynamic_loader=dynamic_loader
    )
    accounts[callee_address] = callee_account

    return callee_account


def get_call_data(
    global_state: GlobalState,
    memory_start: Union[int, Expression],
    memory_size: Union[int, Expression],
):
    """Gets call_data from the global_state.

    :param global_state: state to look in
    :param memory_start: Start index
    :param memory_size: Size
    :return: Tuple containing: call_data array from memory or empty array if symbolic, type found
    """
    state = global_state.mstate
    transaction_id = "{}_internalcall".format(global_state.current_transaction.id)

    memory_start = (
        symbol_factory.BitVecVal(memory_start, 256)
        if isinstance(memory_start, int)
        else memory_start
    )
    memory_size = (
        symbol_factory.BitVecVal(memory_size, 256)
        if isinstance(memory_size, int)
        else memory_size
    )

    try:
        calldata_from_mem = state.memory[
            util.get_concrete_int(memory_start) : util.get_concrete_int(
                memory_start + memory_size
            )
        ]
        call_data = ConcreteCalldata(transaction_id, calldata_from_mem)
        call_data_type = CalldataType.CONCRETE
        log.debug("Calldata: " + str(call_data))
    except TypeError:
        log.debug("Unsupported symbolic calldata offset")
        call_data_type = CalldataType.SYMBOLIC
        call_data = SymbolicCalldata("{}_internalcall".format(transaction_id))

    return call_data, call_data_type


def native_call(
    global_state: GlobalState,
    callee_address: str,
    call_data: BaseCalldata,
    memory_out_offset: Union[int, Expression],
    memory_out_size: Union[int, Expression],
) -> Union[List[GlobalState], None]:
    if not 0 < int(callee_address, 16) < 5:
        return None

    log.debug("Native contract called: " + callee_address)
    try:
        mem_out_start = util.get_concrete_int(memory_out_offset)
        mem_out_sz = util.get_concrete_int(memory_out_size)
    except TypeError:
        log.debug("CALL with symbolic start or offset not supported")
        return [global_state]

    contract_list = ["ecrecover", "sha256", "ripemd160", "identity"]
    call_address_int = int(callee_address, 16)
    native_gas_min, native_gas_max = OPCODE_GAS["NATIVE_COST"](
        global_state.mstate.calculate_extension_size(mem_out_start, mem_out_sz),
        contract_list[call_address_int - 1],
    )
    global_state.mstate.min_gas_used += native_gas_min
    global_state.mstate.max_gas_used += native_gas_max
    global_state.mstate.mem_extend(mem_out_start, mem_out_sz)
    try:
        data = natives.native_contracts(call_address_int, call_data)
    except natives.NativeContractException:
        for i in range(mem_out_sz):
            global_state.mstate.memory[mem_out_start + i] = global_state.new_bitvec(
                contract_list[call_address_int - 1] + "(" + str(call_data) + ")", 8
            )
        return [global_state]

    for i in range(
        min(len(data), mem_out_sz)
    ):  # If more data is used then it's chopped off
        global_state.mstate.memory[mem_out_start + i] = data[i]
    # TODO: maybe use BitVec here constrained to 1
    return [global_state]
