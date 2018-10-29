from mythril.laser.ethereum.transaction.transaction_models import MessageCallTransaction, ContractCreationTransaction, get_next_transaction_id
from z3 import BitVec
from mythril.laser.ethereum.state import GlobalState, Environment, CalldataType, Account, WorldState
from mythril.disassembler.disassembly import Disassembly
from mythril.laser.ethereum.cfg import Node, Edge, JumpType


def execute_message_call(laser_evm, callee_address, caller_address, origin_address, code, data, gas, gas_price, value):
    """ Executes a message call transaction from all open states """
    open_states = laser_evm.open_states[:]
    del laser_evm.open_states[:]

    for open_world_state in open_states:
        transaction = MessageCallTransaction(
            identifier=get_next_transaction_id(),
            world_state=open_world_state,
            callee_account=open_world_state[callee_address],
            caller=caller_address,
            call_data=data,
            gas_price=gas_price,
            call_value=value,
            origin=origin_address,
            call_data_type=CalldataType.SYMBOLIC,
            code=Disassembly(code)
        )

        _setup_global_state_for_execution(laser_evm, transaction)

    laser_evm.exec()


def _setup_global_state_for_execution(laser_evm, transaction):
    """ Sets up global state and cfg for a transactions execution"""
    global_state = transaction.initial_global_state()
    global_state.transaction_stack.append((transaction, None))

    new_node = Node(global_state.environment.active_account.contract_name)

    laser_evm.nodes[new_node.uid] = new_node
    if transaction.world_state.node:
        laser_evm.edges.append(Edge(transaction.world_state.node.uid, new_node.uid, edge_type=JumpType.Transaction,
                               condition=None))
    global_state.node = new_node
    new_node.states.append(global_state)
    laser_evm.graph.add_vertex(global_state)
