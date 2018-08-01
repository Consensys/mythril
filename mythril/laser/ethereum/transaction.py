import logging
from mythril.disassembler.disassembly import Disassembly
from mythril.laser.ethereum.state import GlobalState, Environment, CalldataType, WorldState
from mythril.laser.ethereum.cfg import Node, Edge, JumpType
from z3 import BitVec


class TransactionEndSignal(Exception):
    """ Exception raised when a transaction is finalized"""
    def __init__(self, global_state):
        self.global_state = global_state


class TransactionStartSignal(Exception):
    """ Exception raised when a new transaction is started"""
    def __init__(self, transaction, op_code):
        self.transaction = transaction
        self.op_code = op_code


class MessageCallTransaction:
    """ Transaction object models an transaction"""
    def __init__(self,
                 world_state,
                 callee_account,
                 caller,
                 call_data=(),
                 gas_price=BitVec("gasprice", 256),
                 call_value=BitVec("callvalue", 256),
                 origin=BitVec("origin", 256),
                 call_data_type=BitVec("call_data_type", 256)
                 ):
        assert isinstance(world_state, WorldState)

        self.world_state = world_state
        self.callee_account = callee_account
        self.caller = caller
        self.call_data = call_data
        self.gas_price = gas_price
        self.call_value = call_value
        self.origin = origin
        self.call_data_type = call_data_type

        self.return_data = None

    def initial_global_state(self):
        # Initialize the execution environment
        environment = Environment(
            self.callee_account,
            self.caller,
            self.call_data,
            self.gas_price,
            self.call_value,
            self.origin,
            code=self.callee_account.code,
            calldata_type=self.call_data_type,
        )

        global_state = GlobalState(self.world_state, environment, None)
        global_state.environment.active_function_name = 'fallback'

        return global_state

    def end(self, global_state, return_data=None):
        self.return_data = return_data
        raise TransactionEndSignal(global_state)


