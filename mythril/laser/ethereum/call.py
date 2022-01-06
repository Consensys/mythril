"""This module contains the business logic used by Instruction in
instructions.py to get the necessary elements from the stack and determine the
parameters for the new global state."""

import logging
import re
from typing import Union, List, cast, Optional
from eth.constants import GAS_CALLSTIPEND

import mythril.laser.ethereum.util as util
from mythril.laser.ethereum import natives
from mythril.laser.ethereum.instruction_data import calculate_native_gas
from mythril.laser.ethereum.state.account import Account
from mythril.laser.ethereum.natives import PRECOMPILE_COUNT, PRECOMPILE_FUNCTIONS
from mythril.laser.ethereum.state.calldata import (
    BaseCalldata,
    SymbolicCalldata,
    ConcreteCalldata,
)
from mythril.laser.ethereum.state.global_state import GlobalState
from mythril.laser.smt import BitVec, If
from mythril.laser.smt import simplify, Expression, symbol_factory
from mythril.support.loader import DynLoader

"""
This module contains the business logic used by Instruction in instructions.py
to get the necessary elements from the stack and determine the parameters for the new global state.
"""

log = logging.getLogger(__name__)
SYMBOLIC_CALLDATA_SIZE = 320  # Used when copying symbolic calldata


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
    (
        memory_input_offset,
        memory_input_size,
        memory_out_offset,
        memory_out_size,
    ) = global_state.mstate.pop(4)

    callee_address = get_callee_address(global_state, dynamic_loader, to)

    callee_account = None
    call_data = get_call_data(global_state, memory_input_offset, memory_input_size)
    if isinstance(callee_address, BitVec) or (
        isinstance(callee_address, str)
        and (int(callee_address, 16) > PRECOMPILE_COUNT or int(callee_address, 16) == 0)
    ):
        callee_account = get_callee_account(
            global_state, callee_address, dynamic_loader
        )

    gas = gas + If(value > 0, symbol_factory.BitVecVal(GAS_CALLSTIPEND, gas.size()), 0)
    return (
        callee_address,
        callee_account,
        call_data,
        value,
        gas,
        memory_out_offset,
        memory_out_size,
    )


def _get_padded_hex_address(address: int) -> str:
    hex_address = hex(address)[2:]
    return "0x{}{}".format("0" * (40 - len(hex_address)), hex_address)


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
        callee_address = _get_padded_hex_address(
            util.get_concrete_int(symbolic_to_address)
        )
    except TypeError:
        log.debug("Symbolic call encountered")

        match = re.search(r"Storage\[(\d+)\]", str(simplify(symbolic_to_address)))
        log.debug("CALL to: " + str(simplify(symbolic_to_address)))

        if match is None or dynamic_loader is None:
            return symbolic_to_address

        index = int(match.group(1))
        log.debug("Dynamic contract address at storage index {}".format(index))

        # attempt to read the contract address from instance storage
        try:
            callee_address = dynamic_loader.read_storage(
                "0x{:040X}".format(environment.active_account.address.value), index
            )
        # TODO: verify whether this happens or not
        except:
            return symbolic_to_address

        # testrpc simply returns the address, geth response is more elaborate.
        if not re.match(r"^0x[0-9a-f]{40}$", callee_address):
            callee_address = "0x" + callee_address[26:]

    return callee_address


def get_callee_account(
    global_state: GlobalState,
    callee_address: Union[str, BitVec],
    dynamic_loader: DynLoader,
):
    """Gets the callees account from the global_state.

    :param global_state: state to look in
    :param callee_address: address of the callee
    :param dynamic_loader: dynamic loader to use
    :return: Account belonging to callee
    """
    if isinstance(callee_address, BitVec):
        if callee_address.symbolic:
            return Account(callee_address, balances=global_state.world_state.balances)
        else:
            callee_address = hex(callee_address.value)[2:]

    return global_state.world_state.accounts_exist_or_load(
        callee_address, dynamic_loader
    )


def get_call_data(
    global_state: GlobalState,
    memory_start: Union[int, BitVec],
    memory_size: Union[int, BitVec],
):
    """Gets call_data from the global_state.

    :param global_state: state to look in
    :param memory_start: Start index
    :param memory_size: Size
    :return: Tuple containing: call_data array from memory or empty array if symbolic, type found
    """
    state = global_state.mstate
    transaction_id = "{}_internalcall".format(global_state.current_transaction.id)

    memory_start = cast(
        BitVec,
        (
            symbol_factory.BitVecVal(memory_start, 256)
            if isinstance(memory_start, int)
            else memory_start
        ),
    )
    memory_size = cast(
        BitVec,
        (
            symbol_factory.BitVecVal(memory_size, 256)
            if isinstance(memory_size, int)
            else memory_size
        ),
    )

    if memory_size.symbolic:
        memory_size = SYMBOLIC_CALLDATA_SIZE
    try:
        calldata_from_mem = state.memory[
            util.get_concrete_int(memory_start) : util.get_concrete_int(
                memory_start + memory_size
            )
        ]
        return ConcreteCalldata(transaction_id, calldata_from_mem)
    except TypeError:
        log.debug(
            "Unsupported symbolic memory offset %s size %s", memory_start, memory_size
        )
        return SymbolicCalldata(transaction_id)


def insert_ret_val(global_state: GlobalState):
    retval = global_state.new_bitvec(
        "retval_" + str(global_state.get_current_instruction()["address"]), 256
    )
    global_state.mstate.stack.append(retval)
    global_state.world_state.constraints.append(retval == 1)


def native_call(
    global_state: GlobalState,
    callee_address: Union[str, BitVec],
    call_data: BaseCalldata,
    memory_out_offset: Union[int, Expression],
    memory_out_size: Union[int, Expression],
) -> Optional[List[GlobalState]]:

    if (
        isinstance(callee_address, BitVec)
        or not 0 < int(callee_address, 16) <= PRECOMPILE_COUNT
    ):
        return None

    log.debug("Native contract called: " + callee_address)
    try:
        mem_out_start = util.get_concrete_int(memory_out_offset)
        mem_out_sz = util.get_concrete_int(memory_out_size)
    except TypeError:
        log.debug("CALL with symbolic start or offset not supported")
        return [global_state]

    call_address_int = int(callee_address, 16)
    native_gas_min, native_gas_max = calculate_native_gas(
        global_state.mstate.calculate_extension_size(mem_out_start, mem_out_sz),
        PRECOMPILE_FUNCTIONS[call_address_int - 1].__name__,
    )
    global_state.mstate.min_gas_used += native_gas_min
    global_state.mstate.max_gas_used += native_gas_max
    global_state.mstate.mem_extend(mem_out_start, mem_out_sz)

    try:
        data = natives.native_contracts(call_address_int, call_data)
    except natives.NativeContractException:
        for i in range(mem_out_sz):
            global_state.mstate.memory[mem_out_start + i] = global_state.new_bitvec(
                PRECOMPILE_FUNCTIONS[call_address_int - 1].__name__
                + "("
                + str(call_data)
                + ")",
                8,
            )
        insert_ret_val(global_state)
        return [global_state]

    for i in range(
        min(len(data), mem_out_sz)
    ):  # If more data is used then it's chopped off
        global_state.mstate.memory[mem_out_start + i] = data[i]

    insert_ret_val(global_state)
    return [global_state]
