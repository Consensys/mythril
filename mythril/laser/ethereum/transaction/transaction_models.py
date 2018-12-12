from typing import Union
from mythril.disassembler.disassembly import Disassembly
from mythril.laser.ethereum.state.environment import Environment
from mythril.laser.ethereum.state.calldata import (
    BaseCalldata,
    ConcreteCalldata,
    SymbolicCalldata,
)
from mythril.laser.ethereum.state.account import Account
from mythril.laser.ethereum.state.world_state import WorldState
from mythril.laser.ethereum.state.global_state import GlobalState
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


class BaseTransaction:
    """Basic transaction class holding common data."""

    def __init__(
        self,
        world_state: WorldState,
        callee_account: Account = None,
        caller: ExprRef = None,
        call_data=None,
        identifier=None,
        gas_price=None,
        gas_limit=None,
        origin=None,
        code=None,
        call_data_type=None,
        call_value=None,
        init_call_data=True,
    ):
        assert isinstance(world_state, WorldState)
        self.world_state = world_state
        self.id = identifier or get_next_transaction_id()

        self.gas_price = (
            gas_price
            if gas_price is not None
            else BitVec("gasprice{}".format(identifier), 256)
        )
        self.gas_limit = gas_limit

        self.origin = (
            origin if origin is not None else BitVec("origin{}".format(identifier), 256)
        )
        self.code = code

        self.caller = caller
        self.callee_account = callee_account
        if call_data is None and init_call_data:
            self.call_data = SymbolicCalldata(self.id)
        else:
            self.call_data = call_data if isinstance(call_data, BaseCalldata) else None

        self.call_data_type = (
            call_data_type
            if call_data_type is not None
            else BitVec("call_data_type{}".format(identifier), 256)
        )
        self.call_value = (
            call_value
            if call_value is not None
            else BitVec("callvalue{}".format(identifier), 256)
        )

        self.return_data = None

    def initial_global_state_from_environment(self, environment, active_function):
        # Initialize the execution environment
        global_state = GlobalState(self.world_state, environment, None)
        global_state.environment.active_function_name = active_function
        return global_state


class MessageCallTransaction(BaseTransaction):
    """ Transaction object models an transaction"""

    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)

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
        return super().initial_global_state_from_environment(
            environment, active_function="fallback"
        )

    def end(self, global_state: GlobalState, return_data=None, revert=False) -> None:
        self.return_data = return_data
        raise TransactionEndSignal(global_state, revert)


class ContractCreationTransaction(BaseTransaction):
    """ Transaction object models an transaction"""

    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs, init_call_data=False)
        # TODO: set correct balance for new account
        self.callee_account = self.callee_account or self.world_state.create_account(
            0, concrete_storage=True
        )

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
        return super().initial_global_state_from_environment(
            environment, active_function="constructor"
        )

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
