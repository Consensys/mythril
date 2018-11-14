import logging
from typing import Union
from mythril.disassembler.disassembly import Disassembly
from mythril.laser.ethereum.state import (
    GlobalState,
    Environment,
    WorldState,
    Account,
    Calldata,
)
from z3 import BitVec, ExprRef
import array

_next_transaction_id = 0


def get_next_transaction_id() -> int:
    global _next_transaction_id
    _next_transaction_id += 1
    return _next_transaction_id


class TransactionEndSignal(Exception):
    """ Exception raised when a transaction is finalized"""

    def __init__(self, global_state: GlobalState, revert=False):
        self.global_state = global_state
        self.revert = revert


class TransactionStartSignal(Exception):
    """ Exception raised when a new transaction is started"""

    def __init__(
        self,
        transaction: Union["MessageCallTransaction", "ContractCreationTransaction"],
        op_code: str,
    ):
        self.transaction = transaction
        self.op_code = op_code


class MessageCallTransaction:
    """ Transaction object models an transaction"""

    def __init__(
        self,
        world_state: WorldState,
        callee_account: Account,
        caller: ExprRef,
        call_data=None,
        identifier=None,
        gas_price=None,
        call_value=None,
        origin=None,
        call_data_type=None,
        code=None,
    ):
        assert isinstance(world_state, WorldState)
        self.id = identifier or get_next_transaction_id()
        self.world_state = world_state
        self.callee_account = callee_account
        self.caller = caller
        self.call_data = (
            Calldata(self.id, call_data)
            if not isinstance(call_data, Calldata)
            else call_data
        )
        self.gas_price = (
            BitVec("gasprice{}".format(identifier), 256)
            if gas_price is None
            else gas_price
        )
        self.call_value = (
            BitVec("callvalue{}".format(identifier), 256)
            if call_value is None
            else call_value
        )
        self.origin = (
            BitVec("origin{}".format(identifier), 256) if origin is None else origin
        )
        self.call_data_type = (
            BitVec("call_data_type{}".format(identifier), 256)
            if call_data_type is None
            else call_data_type
        )
        self.code = code
        self.return_data = None

    def initial_global_state(self) -> GlobalState:
        """Initialize the execution environment"""
        environment = Environment(
            self.callee_account,
            self.caller,
            self.call_data,
            self.gas_price,
            self.call_value,
            self.origin,
            code=self.code or self.callee_account.code,
            calldata_type=self.call_data_type,
        )

        global_state = GlobalState(self.world_state, environment, None)
        global_state.environment.active_function_name = "fallback"

        return global_state

    def end(self, global_state: GlobalState, return_data=None, revert=False) -> None:
        self.return_data = return_data
        raise TransactionEndSignal(global_state, revert)


class ContractCreationTransaction:
    """ Transaction object models an transaction"""

    def __init__(
        self,
        world_state: WorldState,
        caller: ExprRef,
        identifier=None,
        callee_account=None,
        code=None,
        call_data=None,
        gas_price=None,
        call_value=None,
        origin=None,
        call_data_type=None,
    ):
        assert isinstance(world_state, WorldState)
        self.id = identifier or get_next_transaction_id()
        self.world_state = world_state
        # TODO: set correct balance for new account
        self.callee_account = (
            callee_account
            if callee_account
            else world_state.create_account(0, concrete_storage=True)
        )

        self.caller = caller

        self.gas_price = (
            BitVec("gasprice{}".format(identifier), 256)
            if gas_price is None
            else gas_price
        )
        self.call_value = (
            BitVec("callvalue{}".format(identifier), 256)
            if call_value is None
            else call_value
        )
        self.origin = (
            BitVec("origin{}".format(identifier), 256) if origin is None else origin
        )
        self.call_data_type = (
            BitVec("call_data_type{}".format(identifier), 256)
            if call_data_type is None
            else call_data_type
        )

        self.call_data = (
            Calldata(self.id, call_data)
            if not isinstance(call_data, Calldata)
            else call_data
        )
        self.origin = origin
        self.code = code
        self.return_data = None

    def initial_global_state(self) -> GlobalState:
        """Initialize the execution environment"""
        environment = Environment(
            self.callee_account,
            self.caller,
            self.call_data,
            self.gas_price,
            self.call_value,
            self.origin,
            self.code,
            calldata_type=self.call_data_type,
        )

        global_state = GlobalState(self.world_state, environment, None)
        global_state.environment.active_function_name = "constructor"

        return global_state

    def end(self, global_state: GlobalState, return_data=None, revert=False):

        if (
            not all([isinstance(element, int) for element in return_data])
            or len(return_data) == 0
        ):
            self.return_data = None
            raise TransactionEndSignal(global_state)

        contract_code = bytes.hex(array.array("B", return_data).tostring())

        global_state.environment.active_account.code = Disassembly(contract_code)
        self.return_data = global_state.environment.active_account.address
        assert global_state.environment.active_account.code.instruction_list != []

        raise TransactionEndSignal(global_state, revert=revert)
