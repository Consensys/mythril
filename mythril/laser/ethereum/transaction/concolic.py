from typing import List, Union
from mythril.laser.ethereum.transaction.transaction_models import (
    MessageCallTransaction,
    ContractCreationTransaction,
    get_next_transaction_id,
)
from z3 import BitVec
from mythril.laser.ethereum.state.environment import Environment
from mythril.laser.ethereum.state.calldata import CalldataType, ConcreteCalldata
from mythril.laser.ethereum.state.account import Account
from mythril.laser.ethereum.state.world_state import WorldState
from mythril.laser.ethereum.state.global_state import GlobalState
from mythril.disassembler.disassembly import Disassembly
from mythril.laser.ethereum.cfg import Node, Edge, JumpType


def execute_message_call(
    laser_evm,
    callee_address,
    caller_address,
    origin_address,
    code,
    data,
    gas_limit,
    gas_price,
    value,
    track_gas=False,
) -> Union[None, List[GlobalState]]:
    """ Executes a message call transaction from all open states """
    # TODO: Resolve circular import between .transaction and ..svm to import LaserEVM here
    open_states = laser_evm.open_states[:]
    del laser_evm.open_states[:]

    for open_world_state in open_states:
        next_transaction_id = get_next_transaction_id()
        transaction = MessageCallTransaction(
            world_state=open_world_state,
            identifier=next_transaction_id,
            gas_price=gas_price,
            gas_limit=gas_limit,
            origin=origin_address,
            code=Disassembly(code),
            caller=caller_address,
            callee_account=open_world_state[callee_address],
            call_data=ConcreteCalldata(next_transaction_id, data),
            call_data_type=CalldataType.SYMBOLIC,
            call_value=value,
        )

        _setup_global_state_for_execution(laser_evm, transaction)

    return laser_evm.exec(track_gas=track_gas)


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
    global_state.node = new_node
    new_node.states.append(global_state)
    laser_evm.work_list.append(global_state)
