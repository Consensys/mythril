"""This module contains functions setting up and executing transactions with
symbolic values."""
import logging
from typing import List

from mythril.laser.smt import symbol_factory, Or, Bool
from mythril.disassembler.disassembly import Disassembly
from mythril.laser.ethereum.cfg import Node, Edge, JumpType
from mythril.laser.ethereum.state.calldata import BaseCalldata, SymbolicCalldata
from mythril.laser.ethereum.state.account import Account
from mythril.laser.ethereum.transaction.transaction_models import (
    MessageCallTransaction,
    ContractCreationTransaction,
    get_next_transaction_id,
)

log = logging.getLogger(__name__)

CREATOR_ADDRESS = 0xAFFEAFFEAFFEAFFEAFFEAFFEAFFEAFFEAFFEAFFE
ATTACKER_ADDRESS = 0xDEADBEEFDEADBEEFDEADBEEFDEADBEEFDEADBEEF


def generate_function_constraints(
    calldata: SymbolicCalldata, func_hashes: List[List[int]]
) -> List[Bool]:
    """
    This will generate constraints for fixing the function call part of calldata
    :param calldata: Calldata
    :param func_hashes: The list of function hashes allowed for this transaction
    :return: Constraints List
    """
    if len(func_hashes) == 0:
        return []
    constraints = []
    for i in range(4):
        constraint = Bool(False)
        for func_hash in func_hashes:
            constraint = Or(
                constraint, calldata[i] == symbol_factory.BitVecVal(func_hash[i], 8)
            )
        constraints.append(constraint)
    return constraints


def execute_message_call(laser_evm, callee_address: str, function_hashes=None) -> None:
    """Executes a message call transaction from all open states.

    :param laser_evm: The laser evm object
    :param callee_address: The address of the callee
    :param function_hashes: The function calls to be constrained for the message call
    """
    # TODO: Resolve circular import between .transaction and ..svm to import LaserEVM here
    open_states = laser_evm.open_states[:]
    del laser_evm.open_states[:]

    for open_world_state in open_states:
        if open_world_state[callee_address].deleted:
            log.debug("Can not execute dead contract, skipping.")
            continue

        next_transaction_id = get_next_transaction_id()
        calldata = SymbolicCalldata(next_transaction_id)
        transaction = MessageCallTransaction(
            world_state=open_world_state,
            identifier=next_transaction_id,
            gas_price=symbol_factory.BitVecSym(
                "gas_price{}".format(next_transaction_id), 256
            ),
            gas_limit=8000000,  # block gas limit
            origin=symbol_factory.BitVecSym(
                "origin{}".format(next_transaction_id), 256
            ),
            caller=symbol_factory.BitVecVal(ATTACKER_ADDRESS, 256),
            callee_account=open_world_state[callee_address],
            call_data=calldata,
            call_value=symbol_factory.BitVecSym(
                "call_value{}".format(next_transaction_id), 256
            ),
        )
        constraints = (
            generate_function_constraints(calldata, function_hashes)
            if function_hashes
            else None
        )
        _setup_global_state_for_execution(laser_evm, transaction, constraints)

    laser_evm.exec()


def execute_contract_creation(
    laser_evm, contract_initialization_code, contract_name=None
) -> Account:
    """Executes a contract creation transaction from all open states.

    :param laser_evm:
    :param contract_initialization_code:
    :param contract_name:
    :return:
    """
    # TODO: Resolve circular import between .transaction and ..svm to import LaserEVM here
    open_states = laser_evm.open_states[:]
    del laser_evm.open_states[:]

    new_account = laser_evm.world_state.create_account(
        0, concrete_storage=True, dynamic_loader=None
    )
    if contract_name:
        new_account.contract_name = contract_name

    for open_world_state in open_states:
        next_transaction_id = get_next_transaction_id()
        transaction = ContractCreationTransaction(
            world_state=open_world_state,
            identifier=next_transaction_id,
            gas_price=symbol_factory.BitVecSym(
                "gas_price{}".format(next_transaction_id), 256
            ),
            gas_limit=8000000,  # block gas limit
            origin=symbol_factory.BitVecSym(
                "origin{}".format(next_transaction_id), 256
            ),
            code=Disassembly(contract_initialization_code),
            caller=symbol_factory.BitVecVal(CREATOR_ADDRESS, 256),
            callee_account=new_account,
            call_data=[],
            call_value=symbol_factory.BitVecSym(
                "call_value{}".format(next_transaction_id), 256
            ),
        )
        _setup_global_state_for_execution(laser_evm, transaction)
    laser_evm.exec(True)

    return new_account


def _setup_global_state_for_execution(
    laser_evm, transaction, initial_constraints=None
) -> None:
    """Sets up global state and cfg for a transactions execution.

    :param laser_evm:
    :param transaction:
    """
    # TODO: Resolve circular import between .transaction and ..svm to import LaserEVM here
    global_state = transaction.initial_global_state()
    global_state.transaction_stack.append((transaction, None))
    global_state.mstate.constraints += initial_constraints or []
    new_node = Node(
        global_state.environment.active_account.contract_name,
        function_name=global_state.environment.active_function_name,
    )
    if laser_evm.requires_statespace:
        laser_evm.nodes[new_node.uid] = new_node

    if transaction.world_state.node:
        if laser_evm.requires_statespace:
            laser_evm.edges.append(
                Edge(
                    transaction.world_state.node.uid,
                    new_node.uid,
                    edge_type=JumpType.Transaction,
                    condition=None,
                )
            )

        global_state.mstate.constraints += transaction.world_state.node.constraints
        new_node.constraints = global_state.mstate.constraints.as_list

    global_state.world_state.transaction_sequence.append(transaction)
    global_state.node = new_node
    new_node.states.append(global_state)
    laser_evm.work_list.append(global_state)
