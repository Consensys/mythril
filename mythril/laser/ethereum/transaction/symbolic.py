"""This module contains functions setting up and executing transactions with
symbolic values."""
import logging
from typing import Optional, List, Union
from copy import deepcopy


from mythril.disassembler.disassembly import Disassembly
from mythril.laser.ethereum.cfg import Node, Edge, JumpType
from mythril.laser.ethereum.state.account import Account
from mythril.laser.ethereum.state.calldata import SymbolicCalldata
from mythril.laser.ethereum.state.constraints import Constraints
from mythril.laser.ethereum.state.world_state import WorldState
from mythril.laser.ethereum.transaction.transaction_models import (
    MessageCallTransaction,
    ContractCreationTransaction,
    tx_id_manager,
    BaseTransaction,
)
from mythril.laser.smt import symbol_factory, Or, Bool, BitVec
from mythril.support.support_args import args as cmd_args


FUNCTION_HASH_BYTE_LENGTH = 4

log = logging.getLogger(__name__)


class Actors:
    def __init__(
        self,
        creator=0xAFFEAFFEAFFEAFFEAFFEAFFEAFFEAFFEAFFEAFFE,
        attacker=0xDEADBEEFDEADBEEFDEADBEEFDEADBEEFDEADBEEF,
        someguy=0xAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA,
    ):
        self.addresses = {
            "CREATOR": symbol_factory.BitVecVal(creator, 256),
            "ATTACKER": symbol_factory.BitVecVal(attacker, 256),
            "SOMEGUY": symbol_factory.BitVecVal(someguy, 256),
        }

    def __setitem__(self, actor: str, address: Optional[str]):
        """
        Sets an actor to a desired address

        :param actor: Name of the actor to set
        :param address: Address to set the actor to. None to delete the actor
        """
        if address is None:
            if actor in ("CREATOR", "ATTACKER"):
                raise ValueError("Can't delete creator or attacker address")
            del self.addresses[actor]
        else:
            if address[0:2] != "0x":
                raise ValueError("Actor address not in valid format")

            self.addresses[actor] = symbol_factory.BitVecVal(int(address[2:], 16), 256)

    def __getitem__(self, actor: str):
        return self.addresses[actor]

    @property
    def creator(self):
        return self.addresses["CREATOR"]

    @property
    def attacker(self):
        return self.addresses["ATTACKER"]

    def __len__(self):
        return len(self.addresses)


ACTORS = Actors()


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
    for i in range(FUNCTION_HASH_BYTE_LENGTH):
        constraint = Bool(False)
        for func_hash in func_hashes:
            if func_hash == -1:
                # Fallback function without calldata
                constraint = Or(constraint, calldata.size < 4)
            elif func_hash == -2:
                # Receive function
                constraint = Or(constraint, calldata.size == 0)
            else:
                constraint = Or(
                    constraint, calldata[i] == symbol_factory.BitVecVal(func_hash[i], 8)
                )
        constraints.append(constraint)
    return constraints


def execute_message_call(
    laser_evm, callee_address: BitVec, func_hashes: List[List[int]] = None
) -> None:
    """Executes a message call transaction from all open states.

    :param laser_evm:
    :param callee_address:
    """
    # TODO: Resolve circular import between .transaction and ..svm to import LaserEVM here
    open_states = laser_evm.open_states[:]
    del laser_evm.open_states[:]

    for open_world_state in open_states:
        if open_world_state[callee_address].deleted:
            log.debug("Can not execute dead contract, skipping.")
            continue

        next_transaction_id = tx_id_manager.get_next_tx_id()

        external_sender = symbol_factory.BitVecSym(
            "sender_{}".format(next_transaction_id), 256
        )
        calldata = SymbolicCalldata(next_transaction_id)
        transaction = MessageCallTransaction(
            world_state=open_world_state,
            identifier=next_transaction_id,
            gas_price=symbol_factory.BitVecSym(
                "gas_price{}".format(next_transaction_id), 256
            ),
            gas_limit=8000000,  # block gas limit
            origin=external_sender,
            caller=external_sender,
            callee_account=open_world_state[callee_address],
            call_data=calldata,
            call_value=symbol_factory.BitVecSym(
                "call_value{}".format(next_transaction_id), 256
            ),
        )
        constraints = (
            generate_function_constraints(calldata, func_hashes)
            if func_hashes
            else None
        )
        _setup_global_state_for_execution(laser_evm, transaction, constraints)

    laser_evm.exec()


def execute_contract_creation(
    laser_evm,
    contract_initialization_code,
    contract_name=None,
    world_state=None,
    origin=ACTORS["CREATOR"],
    caller=ACTORS["CREATOR"],
) -> Account:
    """Executes a contract creation transaction from all open states.

    :param laser_evm:
    :param contract_initialization_code:
    :param contract_name:
    :return:
    """

    world_state = world_state or WorldState()
    open_states = [world_state]
    del laser_evm.open_states[:]
    new_account = None
    for open_world_state in open_states:
        next_transaction_id = tx_id_manager.get_next_tx_id()
        # call_data "should" be '[]', but it is easier to model the calldata symbolically
        # and add logic in codecopy/codesize/calldatacopy/calldatasize than to model code "correctly"
        transaction = ContractCreationTransaction(
            world_state=open_world_state,
            identifier=next_transaction_id,
            gas_price=symbol_factory.BitVecSym(
                "gas_price{}".format(next_transaction_id), 256
            ),
            gas_limit=8000000,  # block gas limit
            origin=origin,
            code=Disassembly(contract_initialization_code),
            caller=caller,
            contract_name=contract_name,
            call_data=None,
            call_value=symbol_factory.BitVecSym(
                "call_value{}".format(next_transaction_id), 256
            ),
        )
        _setup_global_state_for_execution(laser_evm, transaction)
        new_account = new_account or transaction.callee_account

    laser_evm.exec(True)

    return new_account


def _setup_global_state_for_execution(
    laser_evm,
    transaction: BaseTransaction,
    initial_constraints: Optional[List[Bool]] = None,
) -> None:
    """Sets up global state and cfg for a transactions execution.

    :param laser_evm:
    :param transaction:
    """
    # TODO: Resolve circular import between .transaction and ..svm to import LaserEVM here
    global_state = transaction.initial_global_state()
    global_state.transaction_stack.append((transaction, None))
    global_state.world_state.constraints += initial_constraints or []

    global_state.world_state.constraints.append(
        Or(*[transaction.caller == actor for actor in ACTORS.addresses.values()])
    )

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
        new_node.constraints = global_state.world_state.constraints

    global_state.world_state.transaction_sequence.append(transaction)
    global_state.node = new_node
    new_node.states.append(global_state)
    laser_evm.work_list.append(global_state)


def execute_transaction(*args, **kwargs):
    """
    Chooses the transaction type based on callee address and
    executes the transaction
    """
    laser_evm = args[0]
    if kwargs["callee_address"] == "":
        for ws in laser_evm.open_states[:]:
            execute_contract_creation(
                laser_evm=laser_evm,
                contract_initialization_code=kwargs["data"],
                world_state=ws,
            )
        return

    execute_message_call(
        laser_evm=laser_evm,
        callee_address=symbol_factory.BitVecVal(int(kwargs["callee_address"], 16), 256),
    )
