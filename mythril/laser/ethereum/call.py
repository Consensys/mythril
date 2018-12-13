"""
This module contains the business logic used by Instruction in instructions.py
to get the necessary elements from the stack and determine the parameters for the new global state.
"""

import logging
from typing import Union
from z3 import simplify, ExprRef, Extract
import mythril.laser.ethereum.util as util
from mythril.laser.ethereum.state.account import Account
from mythril.laser.ethereum.state.calldata import (
    CalldataType,
    SymbolicCalldata,
    ConcreteCalldata,
)
from mythril.laser.ethereum.state.global_state import GlobalState
from mythril.support.loader import DynLoader
import re


def get_call_parameters(
    global_state: GlobalState, dynamic_loader: DynLoader, with_value=False
):
    """
    Gets call parameters from global state
    Pops the values from the stack and determines output parameters
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
    global_state: GlobalState, dynamic_loader: DynLoader, symbolic_to_address: ExprRef
):
    """
    Gets the address of the callee
    :param global_state: state to look in
    :param dynamic_loader:  dynamic loader to use
    :param symbolic_to_address: The (symbolic) callee address
    :return: Address of the callee
    """
    environment = global_state.environment

    try:
        callee_address = hex(util.get_concrete_int(symbolic_to_address))
    except TypeError:
        logging.debug("Symbolic call encountered")

        match = re.search(r"storage_(\d+)", str(simplify(symbolic_to_address)))
        logging.debug("CALL to: " + str(simplify(symbolic_to_address)))

        if match is None or dynamic_loader is None:
            raise ValueError()

        index = int(match.group(1))
        logging.debug("Dynamic contract address at storage index {}".format(index))

        # attempt to read the contract address from instance storage
        try:
            callee_address = dynamic_loader.read_storage(
                environment.active_account.address, index
            )
        # TODO: verify whether this happens or not
        except:
            logging.debug("Error accessing contract storage.")
            raise ValueError

        # testrpc simply returns the address, geth response is more elaborate.
        if not re.match(r"^0x[0-9a-f]{40}$", callee_address):
            callee_address = "0x" + callee_address[26:]

    return callee_address


def get_callee_account(
    global_state: GlobalState, callee_address: str, dynamic_loader: DynLoader
):
    """
    Gets the callees account from the global_state
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
        logging.debug("Module with address " + callee_address + " not loaded.")

    if dynamic_loader is None:
        raise ValueError()

    logging.debug("Attempting to load dependency")

    try:
        code = dynamic_loader.dynld(environment.active_account.address, callee_address)
    except ValueError as error:
        logging.debug("Unable to execute dynamic loader because: {}".format(str(error)))
        raise error
    if code is None:
        logging.debug("No code returned, not a contract account?")
        raise ValueError()
    logging.debug("Dependency loaded: " + callee_address)

    callee_account = Account(
        callee_address, code, callee_address, dynamic_loader=dynamic_loader
    )
    accounts[callee_address] = callee_account

    return callee_account


def get_call_data(
    global_state: GlobalState,
    memory_start: Union[int, ExprRef],
    memory_size: Union[int, ExprRef],
):
    """
    Gets call_data from the global_state
    :param global_state: state to look in
    :param memory_start: Start index
    :param memory_size: Size
    :return: Tuple containing: call_data array from memory or empty array if symbolic, type found
    """
    state = global_state.mstate
    transaction_id = "{}_internalcall".format(global_state.current_transaction.id)
    try:
        calldata_from_mem = state.memory[
            util.get_concrete_int(memory_start) : util.get_concrete_int(
                memory_start + memory_size
            )
        ]
        i = 0

        call_data = ConcreteCalldata(transaction_id, calldata_from_mem)
        call_data_type = CalldataType.CONCRETE
        logging.debug("Calldata: " + str(call_data))
    except TypeError:
        logging.debug("Unsupported symbolic calldata offset")
        call_data_type = CalldataType.SYMBOLIC
        call_data = SymbolicCalldata("{}_internalcall".format(transaction_id))

    return call_data, call_data_type
