from mythril.disassembler.disassembly import Disassembly
from mythril.laser.ethereum.state import GlobalState, Environment, WorldState
from z3 import BitVec
import array

_next_transaction_id = 0


def get_next_transaction_id():
    global _next_transaction_id
    _next_transaction_id += 1
    return _next_transaction_id


class TransactionEndSignal(Exception):
    """ Exception raised when a transaction is finalized"""

    def __init__(self, global_state, revert=False):
        self.global_state = global_state
        self.revert = revert


class TransactionStartSignal(Exception):
    """ Exception raised when a new transaction is started"""

    def __init__(self, transaction, op_code):
        self.transaction = transaction
        self.op_code = op_code


class ContractTransaction:
    """A base transaction directed at a smart contract."""

    def __init__(
        self,
        world_state,
        caller,
        callee_account=None,
        call_data=(),
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
        self.call_data = call_data
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


class MessageCallTransaction(ContractTransaction):
    """A transaction calling an already existing contract."""

    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)

    def initial_global_state(self):
        # Initialize the execution environment
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

    def end(self, global_state, return_data=None, revert=False):
        self.return_data = return_data
        raise TransactionEndSignal(global_state, revert)


class ContractCreationTransaction(ContractTransaction):
    """A transaction creating a new contract."""

    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        # TODO: set correct balance for new account
        if self.callee_account is None:
            self.callee_account = self.world_state.create_account(
                0, concrete_storage=True
            )

    def initial_global_state(self):
        # Initialize the execution environment
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

    def end(self, global_state, return_data=None, revert=False):

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
