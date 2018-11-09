from z3 import BitVec, Extract, Not
from logging import debug

from mythril.disassembler.disassembly import Disassembly
from mythril.laser.ethereum.cfg import Node, Edge, JumpType
from mythril.laser.ethereum.state import CalldataType, Account, Calldata
from mythril.laser.ethereum.transaction.transaction_models import (
    MessageCallTransaction,
    ContractCreationTransaction,
    get_next_transaction_id,
)


def execute_message_call(laser_evm, callee_address: str) -> None:
    """ Executes a message call transaction from all open states """
    # TODO: Resolve circular import between .transaction and ..svm to import LaserEVM here
    open_states = laser_evm.open_states[:]
    del laser_evm.open_states[:]

    for open_world_state in open_states:
        if open_world_state[callee_address].deleted:
            debug("Can not execute dead contract, skipping.")
            continue

        next_transaction_id = get_next_transaction_id()
        transaction = MessageCallTransaction(
            world_state=open_world_state,
            identifier=next_transaction_id,
            gas_price=BitVec("gas_price{}".format(next_transaction_id), 256),
            gas_limit=8000000,  # block gas limit
            origin=BitVec("origin{}".format(next_transaction_id), 256),
            caller=BitVec("caller{}".format(next_transaction_id), 256),
            callee_account=open_world_state[callee_address],
            call_data=Calldata(next_transaction_id),
            call_data_type=CalldataType.SYMBOLIC,
            call_value=BitVec("call_value{}".format(next_transaction_id), 256),
        )
        _setup_global_state_for_execution(laser_evm, transaction)

    laser_evm.exec()


def execute_contract_creation(
    laser_evm, contract_initialization_code, contract_name=None
) -> Account:
    """ Executes a contract creation transaction from all open states"""
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
            gas_price=BitVec("gas_price{}".format(next_transaction_id), 256),
            gas_limit=8000000,  # block gas limit
            origin=BitVec("origin{}".format(next_transaction_id), 256),
            code=Disassembly(contract_initialization_code),
            caller=BitVec("creator{}".format(next_transaction_id), 256),
            callee_account=new_account,
            call_data=[],
            call_data_type=CalldataType.SYMBOLIC,
            call_value=BitVec("call_value{}".format(next_transaction_id), 256),
        )
        _setup_global_state_for_execution(laser_evm, transaction)
    laser_evm.exec(True)

    return new_account


def _setup_global_state_for_execution(laser_evm, transaction) -> None:
    """ Sets up global state and cfg for a transactions execution"""
    # TODO: Resolve circular import between .transaction and ..svm to import LaserEVM here
    global_state = transaction.initial_global_state()
    global_state.transaction_stack.append((transaction, None))

    new_node = Node(global_state.environment.active_account.contract_name)

    laser_evm.nodes[new_node.uid] = new_node
    if transaction.world_state.node:
        laser_evm.edges.append(
            Edge(
                transaction.world_state.node.uid,
                new_node.uid,
                edge_type=JumpType.Transaction,
                condition=None,
            )
        )

        global_state.mstate.constraints += transaction.world_state.node.constraints
        new_node.constraints = global_state.mstate.constraints

    global_state.world_state.transaction_sequence.append(transaction)
    global_state.node = new_node
    new_node.states.append(global_state)
    laser_evm.work_list.append(global_state)
