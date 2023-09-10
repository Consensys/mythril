"""This module contians the transaction models used throughout LASER's symbolic
execution."""

from copy import deepcopy
from z3 import ExprRef
from typing import Union, Optional
from mythril.support.support_utils import Singleton
from mythril.laser.ethereum.state.calldata import ConcreteCalldata
from mythril.laser.ethereum.state.account import Account
from mythril.laser.ethereum.state.calldata import BaseCalldata, SymbolicCalldata
from mythril.laser.ethereum.state.return_data import ReturnData
from mythril.laser.ethereum.state.environment import Environment
from mythril.laser.ethereum.state.global_state import GlobalState
from mythril.laser.ethereum.state.world_state import WorldState
from mythril.laser.smt import symbol_factory, UGE, BitVec
import logging

log = logging.getLogger(__name__)


class TxIdManager(object, metaclass=Singleton):
    def __init__(self):
        self._next_transaction_id = 0

    def get_next_tx_id(self):
        self._next_transaction_id += 1
        return str(self._next_transaction_id)

    def restart_counter(self):
        self._next_transaction_id = 0

    def set_counter(self, tx_id):
        self._next_transaction_id = tx_id


tx_id_manager = TxIdManager()


class TransactionEndSignal(Exception):
    """Exception raised when a transaction is finalized."""

    def __init__(self, global_state: GlobalState, revert=False) -> None:
        self.global_state = global_state
        self.revert = revert


class TransactionStartSignal(Exception):
    """Exception raised when a new transaction is started."""

    def __init__(
        self,
        transaction: Union["MessageCallTransaction", "ContractCreationTransaction"],
        op_code: str,
        global_state: GlobalState,
    ) -> None:
        self.transaction = transaction
        self.op_code = op_code
        self.global_state = global_state


class BaseTransaction:
    """Basic transaction class holding common data."""

    def __init__(
        self,
        world_state: WorldState,
        callee_account: Account = None,
        caller: ExprRef = None,
        call_data=None,
        identifier: Optional[str] = None,
        gas_price=None,
        gas_limit=None,
        origin=None,
        code=None,
        call_value=None,
        init_call_data=True,
        static=False,
        base_fee=None,
    ) -> None:
        assert isinstance(world_state, WorldState)
        self.world_state = world_state
        self.id = identifier or tx_id_manager.get_next_tx_id()

        self.gas_price = (
            gas_price
            if gas_price is not None
            else symbol_factory.BitVecSym(f"gasprice{identifier}", 256)
        )

        self.base_fee = (
            base_fee
            if base_fee is not None
            else symbol_factory.BitVecSym(f"basefee{identifier}", 256)
        )

        self.gas_limit = gas_limit

        self.origin = (
            origin
            if origin is not None
            else symbol_factory.BitVecSym(f"origin{identifier}", 256)
        )
        self.code = code

        self.caller = caller
        self.callee_account = callee_account
        if call_data is None and init_call_data:
            self.call_data: BaseCalldata = SymbolicCalldata(self.id)
        else:
            self.call_data = (
                call_data
                if isinstance(call_data, BaseCalldata)
                else ConcreteCalldata(self.id, [])
            )

        self.call_value = (
            call_value
            if call_value is not None
            else symbol_factory.BitVecSym(f"callvalue{identifier}", 256)
        )
        self.static = static
        self.return_data: Optional[ReturnData] = None

    def initial_global_state_from_environment(self, environment, active_function):
        """

        :param environment:
        :param active_function:
        :return:
        """
        # Initialize the execution environment
        global_state = GlobalState(self.world_state, environment, None)
        global_state.environment.active_function_name = active_function

        sender = environment.sender
        receiver = environment.active_account.address
        value = (
            environment.callvalue
            if isinstance(environment.callvalue, BitVec)
            else symbol_factory.BitVecVal(environment.callvalue, 256)
        )

        global_state.world_state.constraints.append(
            UGE(global_state.world_state.balances[sender], value)
        )
        global_state.world_state.balances[receiver] += value
        global_state.world_state.balances[sender] -= value

        return global_state

    def initial_global_state(self) -> GlobalState:
        raise NotImplementedError

    def __str__(self) -> str:
        if self.callee_account is None or self.callee_account.address.symbolic is False:
            return "{} {} from {} to {:#42x}".format(
                self.__class__.__name__,
                self.id,
                self.caller,
                int(str(self.callee_account.address)) if self.callee_account else -1,
            )
        else:
            return "{} {} from {} to {}".format(
                self.__class__.__name__,
                self.id,
                self.caller,
                str(self.callee_account.address),
            )


class MessageCallTransaction(BaseTransaction):
    """Transaction object models an transaction."""

    def __init__(self, *args, **kwargs) -> None:
        super().__init__(*args, **kwargs)

    def initial_global_state(self) -> GlobalState:
        """Initialize the execution environment."""
        environment = Environment(
            self.callee_account,
            self.caller,
            self.call_data,
            self.gas_price,
            self.call_value,
            self.origin,
            self.base_fee,
            code=self.code or self.callee_account.code,
            static=self.static,
        )
        return super().initial_global_state_from_environment(
            environment, active_function="fallback"
        )

    def end(self, global_state: GlobalState, return_data=None, revert=False) -> None:
        """

        :param global_state:
        :param return_data:
        :param revert:
        """
        self.return_data = return_data

        raise TransactionEndSignal(global_state, revert)


class ContractCreationTransaction(BaseTransaction):
    """Transaction object models an transaction."""

    def __init__(
        self,
        world_state: WorldState,
        caller: ExprRef = None,
        call_data=None,
        identifier: Optional[str] = None,
        gas_price=None,
        gas_limit=None,
        origin=None,
        code=None,
        call_value=None,
        contract_name=None,
        contract_address=None,
        base_fee=None,
    ) -> None:
        self.prev_world_state = deepcopy(world_state)
        contract_address = (
            contract_address if isinstance(contract_address, int) else None
        )
        callee_account = world_state.create_account(
            0, concrete_storage=True, creator=caller.value, address=contract_address
        )
        callee_account.contract_name = contract_name or callee_account.contract_name
        # init_call_data "should" be false, but it is easier to model the calldata symbolically
        # and add logic in codecopy/codesize/calldatacopy/calldatasize than to model code "correctly"
        super().__init__(
            world_state=world_state,
            callee_account=callee_account,
            caller=caller,
            call_data=call_data,
            identifier=identifier,
            gas_price=gas_price,
            gas_limit=gas_limit,
            origin=origin,
            code=code,
            call_value=call_value,
            init_call_data=True,
            base_fee=base_fee,
        )

    def initial_global_state(self) -> GlobalState:
        """Initialize the execution environment."""
        environment = Environment(
            active_account=self.callee_account,
            sender=self.caller,
            calldata=self.call_data,
            gasprice=self.gas_price,
            callvalue=self.call_value,
            origin=self.origin,
            basefee=self.base_fee,
            code=self.code,
        )
        return super().initial_global_state_from_environment(
            environment, active_function="constructor"
        )

    def end(self, global_state: GlobalState, return_data=None, revert=False):
        """

        :param global_state:
        :param return_data:
        :param revert:
        """

        if return_data is None or return_data.size == 0:
            self.return_data = None
            raise TransactionEndSignal(global_state, revert=revert)

        global_state.environment.active_account.code.assign_bytecode(
            tuple(return_data.return_data)
        )
        return_data = str(hex(global_state.environment.active_account.address.value))
        self.return_data: Optional[ReturnData] = ReturnData(
            return_data, symbol_factory.BitVecVal(len(return_data) // 2, 256)
        )
        assert global_state.environment.active_account.code.instruction_list != []

        raise TransactionEndSignal(global_state, revert=revert)
