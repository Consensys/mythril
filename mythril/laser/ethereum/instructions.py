"""This module contains a representation class for EVM instructions and
transitions between them."""
import logging

from copy import copy, deepcopy
from typing import cast, Callable, List, Union, Tuple

from mythril.laser.smt import (
    Extract,
    Expression,
    UDiv,
    simplify,
    Concat,
    ULT,
    UGT,
    BitVec,
    is_false,
    URem,
    SRem,
    If,
    Bool,
    Not,
    LShR,
    UGE,
)
from mythril.laser.smt import symbol_factory

from mythril.disassembler.disassembly import Disassembly

from mythril.laser.ethereum.state.calldata import ConcreteCalldata, SymbolicCalldata

import mythril.laser.ethereum.util as helper
from mythril.laser.ethereum import util
from mythril.laser.ethereum.function_managers import (
    keccak_function_manager,
    exponent_function_manager,
)

from mythril.laser.ethereum.call import (
    get_call_parameters,
    native_call,
    get_call_data,
    SYMBOLIC_CALLDATA_SIZE,
)
from mythril.laser.ethereum.evm_exceptions import (
    VmException,
    StackUnderflowException,
    InvalidJumpDestination,
    InvalidInstruction,
    OutOfGasException,
    WriteProtection,
)
from mythril.laser.ethereum.instruction_data import get_opcode_gas, calculate_sha3_gas
from mythril.laser.ethereum.state.global_state import GlobalState
from mythril.laser.ethereum.transaction import (
    MessageCallTransaction,
    TransactionStartSignal,
    ContractCreationTransaction,
    get_next_transaction_id,
)

from mythril.support.support_utils import get_code_hash

from mythril.support.loader import DynLoader

log = logging.getLogger(__name__)

TT256 = symbol_factory.BitVecVal(0, 256)
TT256M1 = symbol_factory.BitVecVal(2 ** 256 - 1, 256)


def transfer_ether(
    global_state: GlobalState,
    sender: BitVec,
    receiver: BitVec,
    value: Union[int, BitVec],
):
    """
    Perform an Ether transfer between two accounts

    :param global_state: The global state in which the Ether transfer occurs
    :param sender: The sender of the Ether
    :param receiver: The recipient of the Ether
    :param value: The amount of Ether to send
    :return:
    """
    value = value if isinstance(value, BitVec) else symbol_factory.BitVecVal(value, 256)

    global_state.world_state.constraints.append(
        UGE(global_state.world_state.balances[sender], value)
    )
    global_state.world_state.balances[receiver] += value
    global_state.world_state.balances[sender] -= value


class StateTransition(object):
    """Decorator that handles global state copy and original return.

    This decorator calls the decorated instruction mutator function on a
    copy of the state that is passed to it. After the call, the
    resulting new states' program counter is automatically incremented
    if `increment_pc=True`.
    """

    def __init__(
        self, increment_pc=True, enable_gas=True, is_state_mutation_instruction=False
    ):
        """

        :param increment_pc:
        :param enable_gas:
        :param is_state_mutation_instruction: The function mutates state
        """
        self.increment_pc = increment_pc
        self.enable_gas = enable_gas
        self.is_state_mutation_instruction = is_state_mutation_instruction

    @staticmethod
    def call_on_state_copy(func: Callable, func_obj: "Instruction", state: GlobalState):
        """

        :param func:
        :param func_obj:
        :param state:
        :return:
        """
        global_state_copy = copy(state)
        return func(func_obj, global_state_copy)

    def increment_states_pc(self, states: List[GlobalState]) -> List[GlobalState]:
        """

        :param states:
        :return:
        """
        if self.increment_pc:
            for state in states:
                state.mstate.pc += 1
        return states

    @staticmethod
    def check_gas_usage_limit(global_state: GlobalState):
        """

        :param global_state:
        :return:
        """
        global_state.mstate.check_gas()
        if isinstance(global_state.current_transaction.gas_limit, BitVec):
            value = global_state.current_transaction.gas_limit.value
            if value is None:
                return
            global_state.current_transaction.gas_limit = value
        if (
            global_state.mstate.min_gas_used
            >= global_state.current_transaction.gas_limit
        ):
            raise OutOfGasException()

    def accumulate_gas(self, global_state: GlobalState):
        """

        :param global_state:
        :return:
        """
        if not self.enable_gas:
            return global_state
        opcode = global_state.instruction["opcode"]
        min_gas, max_gas = get_opcode_gas(opcode)
        global_state.mstate.min_gas_used += min_gas
        global_state.mstate.max_gas_used += max_gas
        self.check_gas_usage_limit(global_state)

        return global_state

    def __call__(self, func: Callable) -> Callable:
        def wrapper(
            func_obj: "Instruction", global_state: GlobalState
        ) -> List[GlobalState]:
            """

            :param func_obj:
            :param global_state:
            :return:
            """
            if self.is_state_mutation_instruction and global_state.environment.static:
                raise WriteProtection(
                    "The function {} cannot be executed in a static call".format(
                        func.__name__[:-1]
                    )
                )

            new_global_states = self.call_on_state_copy(func, func_obj, global_state)
            new_global_states = [
                self.accumulate_gas(state) for state in new_global_states
            ]
            return self.increment_states_pc(new_global_states)

        return wrapper


class Instruction:
    """Instruction class is used to mutate a state according to the current
    instruction."""

    def __init__(
        self,
        op_code: str,
        dynamic_loader: DynLoader,
        pre_hooks: List[Callable] = None,
        post_hooks: List[Callable] = None,
    ) -> None:
        """

        :param op_code:
        :param dynamic_loader:
        :param iprof:
        """
        self.dynamic_loader = dynamic_loader
        self.op_code = op_code.upper()
        self.pre_hook = pre_hooks if pre_hooks else []
        self.post_hook = post_hooks if post_hooks else []

    def _execute_pre_hooks(self, global_state: GlobalState):
        for hook in self.pre_hook:
            hook(global_state)

    def _execute_post_hooks(self, global_state: GlobalState):
        for hook in self.post_hook:
            hook(global_state)

    def evaluate(self, global_state: GlobalState, post=False) -> List[GlobalState]:
        """Performs the mutation for this instruction.

        :param global_state:
        :param post:
        :return:
        """
        # Generalize some ops
        log.debug("Evaluating %s at %i", self.op_code, global_state.mstate.pc)

        op = self.op_code.lower()
        if self.op_code.startswith("PUSH"):
            op = "push"
        elif self.op_code.startswith("DUP"):
            op = "dup"
        elif self.op_code.startswith("SWAP"):
            op = "swap"
        elif self.op_code.startswith("LOG"):
            op = "log"

        instruction_mutator = (
            getattr(self, op + "_", None)
            if not post
            else getattr(self, op + "_" + "post", None)
        )
        if instruction_mutator is None:
            raise NotImplementedError

        self._execute_pre_hooks(global_state)
        result = instruction_mutator(global_state)
        self._execute_post_hooks(global_state)

        return result

    @StateTransition()
    def jumpdest_(self, global_state: GlobalState) -> List[GlobalState]:
        """

        :param global_state:
        :return:
        """
        return [global_state]

    @StateTransition()
    def push_(self, global_state: GlobalState) -> List[GlobalState]:
        """

        :param global_state:
        :return:
        """
        push_instruction = global_state.get_current_instruction()
        push_value = push_instruction["argument"]
        try:
            length_of_value = 2 * int(push_instruction["opcode"][4:])
        except ValueError:
            raise VmException("Invalid Push instruction")

        if type(push_value) == tuple:
            if type(push_value[0]) == int:
                new_value = symbol_factory.BitVecVal(push_value[0], 8)
            else:
                new_value = push_value[0]
            if len(push_value) > 1:
                for val in push_value[1:]:
                    if type(val) == int:
                        new_value = Concat(new_value, symbol_factory.BitVecVal(val, 8))
                    else:
                        new_value = Concat(new_value, val)

            pad_length = length_of_value // 2 - len(push_value)

            if pad_length > 0:
                new_value = Concat(new_value, symbol_factory.BitVecVal(0, pad_length))
            if new_value.size() < 256:
                new_value = Concat(
                    symbol_factory.BitVecVal(0, 256 - new_value.size()), new_value
                )

            global_state.mstate.stack.append(new_value)

        else:
            push_value += "0" * max(length_of_value - (len(push_value) - 2), 0)
            global_state.mstate.stack.append(
                symbol_factory.BitVecVal(int(push_value, 16), 256)
            )
        return [global_state]

    @StateTransition()
    def dup_(self, global_state: GlobalState) -> List[GlobalState]:
        """

        :param global_state:
        :return:
        """
        value = int(global_state.get_current_instruction()["opcode"][3:], 10)
        global_state.mstate.stack.append(global_state.mstate.stack[-value])
        return [global_state]

    @StateTransition()
    def swap_(self, global_state: GlobalState) -> List[GlobalState]:
        """

        :param global_state:
        :return:
        """
        depth = int(self.op_code[4:])
        stack = global_state.mstate.stack
        stack[-depth - 1], stack[-1] = stack[-1], stack[-depth - 1]
        return [global_state]

    @StateTransition()
    def pop_(self, global_state: GlobalState) -> List[GlobalState]:
        """

        :param global_state:
        :return:
        """
        global_state.mstate.stack.pop()
        return [global_state]

    @StateTransition()
    def and_(self, global_state: GlobalState) -> List[GlobalState]:
        """

        :param global_state:
        :return:
        """
        stack = global_state.mstate.stack
        op1, op2 = stack.pop(), stack.pop()
        if isinstance(op1, Bool):
            op1 = If(
                op1, symbol_factory.BitVecVal(1, 256), symbol_factory.BitVecVal(0, 256)
            )
        if isinstance(op2, Bool):
            op2 = If(
                op2, symbol_factory.BitVecVal(1, 256), symbol_factory.BitVecVal(0, 256)
            )
        if not isinstance(op1, Expression):
            op1 = symbol_factory.BitVecVal(op1, 256)
        if not isinstance(op2, Expression):
            op2 = symbol_factory.BitVecVal(op2, 256)
        stack.append(op1 & op2)

        return [global_state]

    @StateTransition()
    def or_(self, global_state: GlobalState) -> List[GlobalState]:
        """

        :param global_state:
        :return:
        """
        stack = global_state.mstate.stack
        op1, op2 = stack.pop(), stack.pop()

        if isinstance(op1, Bool):
            op1 = If(
                op1, symbol_factory.BitVecVal(1, 256), symbol_factory.BitVecVal(0, 256)
            )

        if isinstance(op2, Bool):
            op2 = If(
                op2, symbol_factory.BitVecVal(1, 256), symbol_factory.BitVecVal(0, 256)
            )

        stack.append(op1 | op2)

        return [global_state]

    @StateTransition()
    def xor_(self, global_state: GlobalState) -> List[GlobalState]:
        """

        :param global_state:
        :return:
        """
        mstate = global_state.mstate
        mstate.stack.append(mstate.stack.pop() ^ mstate.stack.pop())
        return [global_state]

    @StateTransition()
    def not_(self, global_state: GlobalState):
        """

        :param global_state:
        :return:
        """
        mstate = global_state.mstate
        mstate.stack.append(TT256M1 - mstate.stack.pop())
        return [global_state]

    @StateTransition()
    def byte_(self, global_state: GlobalState) -> List[GlobalState]:
        """

        :param global_state:
        :return:
        """
        mstate = global_state.mstate
        op0, op1 = mstate.stack.pop(), mstate.stack.pop()
        if not isinstance(op1, Expression):
            op1 = symbol_factory.BitVecVal(op1, 256)
        try:
            index = util.get_concrete_int(op0)
            offset = (31 - index) * 8
            if offset >= 0:
                result = simplify(
                    Concat(
                        symbol_factory.BitVecVal(0, 248),
                        Extract(offset + 7, offset, op1),
                    )
                )  # type: Union[int, Expression]
            else:
                result = 0
        except TypeError:
            log.debug("BYTE: Unsupported symbolic byte offset")
            result = global_state.new_bitvec(
                str(simplify(op1)) + "[" + str(simplify(op0)) + "]", 256
            )

        mstate.stack.append(result)
        return [global_state]

    # Arithmetic
    @StateTransition()
    def add_(self, global_state: GlobalState) -> List[GlobalState]:
        """

        :param global_state:
        :return:
        """
        global_state.mstate.stack.append(
            (
                helper.pop_bitvec(global_state.mstate)
                + helper.pop_bitvec(global_state.mstate)
            )
        )
        return [global_state]

    @StateTransition()
    def sub_(self, global_state: GlobalState) -> List[GlobalState]:
        """

        :param global_state:
        :return:
        """
        global_state.mstate.stack.append(
            (
                helper.pop_bitvec(global_state.mstate)
                - helper.pop_bitvec(global_state.mstate)
            )
        )
        return [global_state]

    @StateTransition()
    def mul_(self, global_state: GlobalState) -> List[GlobalState]:
        """

        :param global_state:
        :return:
        """
        global_state.mstate.stack.append(
            (
                helper.pop_bitvec(global_state.mstate)
                * helper.pop_bitvec(global_state.mstate)
            )
        )

        return [global_state]

    @StateTransition()
    def div_(self, global_state: GlobalState) -> List[GlobalState]:
        """

        :param global_state:
        :return:
        """
        op0, op1 = (
            util.pop_bitvec(global_state.mstate),
            util.pop_bitvec(global_state.mstate),
        )
        if op1 == 0:
            global_state.mstate.stack.append(symbol_factory.BitVecVal(0, 256))
        else:
            global_state.mstate.stack.append(UDiv(op0, op1))
        return [global_state]

    @StateTransition()
    def sdiv_(self, global_state: GlobalState) -> List[GlobalState]:
        """

        :param global_state:
        :return:
        """
        s0, s1 = (
            util.pop_bitvec(global_state.mstate),
            util.pop_bitvec(global_state.mstate),
        )
        if s1 == 0:
            global_state.mstate.stack.append(symbol_factory.BitVecVal(0, 256))
        else:
            global_state.mstate.stack.append(s0 / s1)
        return [global_state]

    @StateTransition()
    def mod_(self, global_state: GlobalState) -> List[GlobalState]:
        """

        :param global_state:
        :return:
        """
        s0, s1 = (
            util.pop_bitvec(global_state.mstate),
            util.pop_bitvec(global_state.mstate),
        )
        global_state.mstate.stack.append(0 if s1 == 0 else URem(s0, s1))
        return [global_state]

    @StateTransition()
    def shl_(self, global_state: GlobalState) -> List[GlobalState]:
        shift, value = (
            util.pop_bitvec(global_state.mstate),
            util.pop_bitvec(global_state.mstate),
        )
        global_state.mstate.stack.append(value << shift)
        return [global_state]

    @StateTransition()
    def shr_(self, global_state: GlobalState) -> List[GlobalState]:
        shift, value = (
            util.pop_bitvec(global_state.mstate),
            util.pop_bitvec(global_state.mstate),
        )
        global_state.mstate.stack.append(LShR(value, shift))
        return [global_state]

    @StateTransition()
    def sar_(self, global_state: GlobalState) -> List[GlobalState]:
        shift, value = (
            util.pop_bitvec(global_state.mstate),
            util.pop_bitvec(global_state.mstate),
        )
        global_state.mstate.stack.append(value >> shift)
        return [global_state]

    @StateTransition()
    def smod_(self, global_state: GlobalState) -> List[GlobalState]:
        """

        :param global_state:
        :return:
        """
        s0, s1 = (
            util.pop_bitvec(global_state.mstate),
            util.pop_bitvec(global_state.mstate),
        )
        global_state.mstate.stack.append(0 if s1 == 0 else SRem(s0, s1))
        return [global_state]

    @StateTransition()
    def addmod_(self, global_state: GlobalState) -> List[GlobalState]:
        """

        :param global_state:
        :return:
        """
        s0, s1, s2 = (
            util.pop_bitvec(global_state.mstate),
            util.pop_bitvec(global_state.mstate),
            util.pop_bitvec(global_state.mstate),
        )
        global_state.mstate.stack.append(URem(URem(s0, s2) + URem(s1, s2), s2))
        return [global_state]

    @StateTransition()
    def mulmod_(self, global_state: GlobalState) -> List[GlobalState]:
        """

        :param global_state:
        :return:
        """
        s0, s1, s2 = (
            util.pop_bitvec(global_state.mstate),
            util.pop_bitvec(global_state.mstate),
            util.pop_bitvec(global_state.mstate),
        )
        global_state.mstate.stack.append(URem(URem(s0, s2) * URem(s1, s2), s2))
        return [global_state]

    @StateTransition()
    def exp_(self, global_state: GlobalState) -> List[GlobalState]:
        """

        :param global_state:
        :return:
        """
        state = global_state.mstate
        base, exponent = util.pop_bitvec(state), util.pop_bitvec(state)
        exponentiation, constraint = exponent_function_manager.create_condition(
            base, exponent
        )
        state.stack.append(exponentiation)
        global_state.world_state.constraints.append(constraint)
        return [global_state]

    @StateTransition()
    def signextend_(self, global_state: GlobalState) -> List[GlobalState]:
        """

        :param global_state:
        :return:
        """
        mstate = global_state.mstate
        s0, s1 = mstate.stack.pop(), mstate.stack.pop()

        testbit = s0 * symbol_factory.BitVecVal(8, 256) + symbol_factory.BitVecVal(
            7, 256
        )
        set_testbit = symbol_factory.BitVecVal(1, 256) << testbit
        sign_bit_set = simplify(Not(s1 & set_testbit == 0))

        mstate.stack.append(
            simplify(
                If(
                    s0 <= 31,
                    If(
                        sign_bit_set, s1 | (TT256 - set_testbit), s1 & (set_testbit - 1)
                    ),
                    s1,
                )
            )
        )

        return [global_state]

    # Comparisons
    @StateTransition()
    def lt_(self, global_state: GlobalState) -> List[GlobalState]:
        """

        :param global_state:
        :return:
        """
        state = global_state.mstate
        exp = ULT(util.pop_bitvec(state), util.pop_bitvec(state))
        state.stack.append(exp)
        return [global_state]

    @StateTransition()
    def gt_(self, global_state: GlobalState) -> List[GlobalState]:
        """

        :param global_state:
        :return:
        """
        state = global_state.mstate
        op1, op2 = util.pop_bitvec(state), util.pop_bitvec(state)
        exp = UGT(op1, op2)
        state.stack.append(exp)
        return [global_state]

    @StateTransition()
    def slt_(self, global_state: GlobalState) -> List[GlobalState]:
        """

        :param global_state:
        :return:
        """
        state = global_state.mstate
        exp = util.pop_bitvec(state) < util.pop_bitvec(state)
        state.stack.append(exp)
        return [global_state]

    @StateTransition()
    def sgt_(self, global_state: GlobalState) -> List[GlobalState]:
        """

        :param global_state:
        :return:
        """
        state = global_state.mstate

        exp = util.pop_bitvec(state) > util.pop_bitvec(state)
        state.stack.append(exp)
        return [global_state]

    @StateTransition()
    def eq_(self, global_state: GlobalState) -> List[GlobalState]:
        """

        :param global_state:
        :return:
        """
        state = global_state.mstate

        op1 = state.stack.pop()
        op2 = state.stack.pop()

        if isinstance(op1, Bool):
            op1 = If(
                op1, symbol_factory.BitVecVal(1, 256), symbol_factory.BitVecVal(0, 256)
            )

        if isinstance(op2, Bool):
            op2 = If(
                op2, symbol_factory.BitVecVal(1, 256), symbol_factory.BitVecVal(0, 256)
            )

        exp = op1 == op2

        state.stack.append(exp)
        return [global_state]

    @StateTransition()
    def iszero_(self, global_state: GlobalState) -> List[GlobalState]:
        """

        :param global_state:
        :return:
        """
        state = global_state.mstate
        val = state.stack.pop()
        exp = Not(val) if isinstance(val, Bool) else val == 0

        exp = If(
            exp, symbol_factory.BitVecVal(1, 256), symbol_factory.BitVecVal(0, 256)
        )
        state.stack.append(simplify(exp))

        return [global_state]

    # Call data
    @StateTransition()
    def callvalue_(self, global_state: GlobalState) -> List[GlobalState]:
        """

        :param global_state:
        :return:
        """
        state = global_state.mstate
        environment = global_state.environment
        state.stack.append(environment.callvalue)

        return [global_state]

    @StateTransition()
    def calldataload_(self, global_state: GlobalState) -> List[GlobalState]:
        """

        :param global_state:
        :return:
        """
        state = global_state.mstate
        environment = global_state.environment
        op0 = state.stack.pop()

        value = environment.calldata.get_word_at(op0)

        state.stack.append(value)

        return [global_state]

    @StateTransition()
    def calldatasize_(self, global_state: GlobalState) -> List[GlobalState]:
        """

        :param global_state:
        :return:
        """
        global_state.mstate.stack.append(global_state.environment.calldata.calldatasize)
        return [global_state]

    @staticmethod
    def _calldata_copy_helper(global_state, mstate, mstart, dstart, size):
        environment = global_state.environment

        try:
            mstart = util.get_concrete_int(mstart)
        except TypeError:
            log.debug("Unsupported symbolic memory offset in CALLDATACOPY")
            return [global_state]

        try:
            dstart = util.get_concrete_int(dstart)  # type: Union[int, BitVec]
        except TypeError:
            log.debug("Unsupported symbolic calldata offset in CALLDATACOPY")
            dstart = simplify(dstart)

        try:
            size = util.get_concrete_int(size)  # type: Union[int, BitVec]
        except TypeError:
            log.debug("Unsupported symbolic size in CALLDATACOPY")
            size = SYMBOLIC_CALLDATA_SIZE  # The excess size will get overwritten

        size = cast(int, size)
        if size > 0:
            try:
                mstate.mem_extend(mstart, size)
            except TypeError as e:
                log.debug("Memory allocation error: {}".format(e))
                mstate.mem_extend(mstart, 1)
                mstate.memory[mstart] = global_state.new_bitvec(
                    "calldata_"
                    + str(environment.active_account.contract_name)
                    + "["
                    + str(dstart)
                    + ": + "
                    + str(size)
                    + "]",
                    8,
                )
                return [global_state]

            try:
                i_data = dstart
                new_memory = []
                for i in range(size):
                    value = environment.calldata[i_data]
                    new_memory.append(value)

                    i_data = (
                        i_data + 1
                        if isinstance(i_data, int)
                        else simplify(cast(BitVec, i_data) + 1)
                    )
                for i in range(len(new_memory)):
                    mstate.memory[i + mstart] = new_memory[i]

            except IndexError:
                log.debug("Exception copying calldata to memory")

                mstate.memory[mstart] = global_state.new_bitvec(
                    "calldata_"
                    + str(environment.active_account.contract_name)
                    + "["
                    + str(dstart)
                    + ": + "
                    + str(size)
                    + "]",
                    8,
                )
        return [global_state]

    @StateTransition()
    def calldatacopy_(self, global_state: GlobalState) -> List[GlobalState]:
        """

        :param global_state:
        :return:
        """
        state = global_state.mstate
        op0, op1, op2 = state.stack.pop(), state.stack.pop(), state.stack.pop()

        if isinstance(global_state.current_transaction, ContractCreationTransaction):
            log.debug("Attempt to use CALLDATACOPY in creation transaction")
            return [global_state]

        return self._calldata_copy_helper(global_state, state, op0, op1, op2)

    # Environment
    @StateTransition()
    def address_(self, global_state: GlobalState) -> List[GlobalState]:
        """

        :param global_state:
        :return:
        """
        state = global_state.mstate
        environment = global_state.environment
        state.stack.append(environment.address)
        return [global_state]

    @StateTransition()
    def balance_(self, global_state: GlobalState) -> List[GlobalState]:
        """

        :param global_state:
        :return:
        """
        state = global_state.mstate
        address = state.stack.pop()
        if address.symbolic is False:
            balance = global_state.world_state.accounts_exist_or_load(
                address.value, self.dynamic_loader
            ).balance()
        else:
            balance = symbol_factory.BitVecVal(0, 256)
            for account in global_state.world_state.accounts.values():
                balance = If(address == account.address, account.balance(), balance)
        state.stack.append(balance)
        return [global_state]

    @StateTransition()
    def origin_(self, global_state: GlobalState) -> List[GlobalState]:
        """

        :param global_state:
        :return:
        """
        state = global_state.mstate
        environment = global_state.environment
        state.stack.append(environment.origin)
        return [global_state]

    @StateTransition()
    def caller_(self, global_state: GlobalState) -> List[GlobalState]:
        """

        :param global_state:
        :return:
        """
        state = global_state.mstate
        environment = global_state.environment
        state.stack.append(environment.sender)
        return [global_state]

    @StateTransition()
    def chainid_(self, global_state: GlobalState) -> List[GlobalState]:
        """

        :param global_state:
        :return:
        """
        global_state.mstate.stack.append(global_state.environment.chainid)
        return [global_state]

    @StateTransition()
    def selfbalance_(self, global_state: GlobalState) -> List[GlobalState]:
        """

        :param global_state:
        :return:
        """
        balance = global_state.environment.active_account.balance()
        global_state.mstate.stack.append(balance)
        return [global_state]

    @StateTransition()
    def codesize_(self, global_state: GlobalState) -> List[GlobalState]:
        """

        :param global_state:
        :return:
        """
        state = global_state.mstate
        environment = global_state.environment
        disassembly = environment.code
        calldata = global_state.environment.calldata
        if isinstance(global_state.current_transaction, ContractCreationTransaction):
            # Hacky way to ensure constructor arguments work - Pick some reasonably large size.
            no_of_bytes = len(disassembly.bytecode) // 2
            if isinstance(calldata, ConcreteCalldata):
                no_of_bytes += calldata.size
            else:
                no_of_bytes += 0x200  # space for 16 32-byte arguments
                global_state.world_state.constraints.append(
                    global_state.environment.calldata.size == no_of_bytes
                )

        else:
            no_of_bytes = len(disassembly.bytecode) // 2
        state.stack.append(no_of_bytes)
        return [global_state]

    @staticmethod
    def _sha3_gas_helper(global_state, length):
        min_gas, max_gas = calculate_sha3_gas(length)
        global_state.mstate.min_gas_used += min_gas
        global_state.mstate.max_gas_used += max_gas
        StateTransition.check_gas_usage_limit(global_state)
        return global_state

    @StateTransition(enable_gas=False)
    def sha3_(self, global_state: GlobalState) -> List[GlobalState]:
        """

        :param global_state:
        :return:
        """

        state = global_state.mstate
        index, op1 = state.stack.pop(), state.stack.pop()

        try:
            length = util.get_concrete_int(op1)
        except TypeError:
            # Can't access symbolic memory offsets
            length = 64
            global_state.world_state.constraints.append(op1 == length)
        Instruction._sha3_gas_helper(global_state, length)

        state.mem_extend(index, length)
        data_list = [
            b if isinstance(b, BitVec) else symbol_factory.BitVecVal(b, 8)
            for b in state.memory[index : index + length]
        ]

        if len(data_list) > 1:
            data = simplify(Concat(data_list))
        elif len(data_list) == 1:
            data = data_list[0]
        else:
            # TODO: handle finding x where func(x)==func("")
            result = keccak_function_manager.get_empty_keccak_hash()
            state.stack.append(result)
            return [global_state]

        result = keccak_function_manager.create_keccak(data)
        state.stack.append(result)

        return [global_state]

    @StateTransition()
    def gasprice_(self, global_state: GlobalState) -> List[GlobalState]:
        """

        :param global_state:
        :return:
        """
        global_state.mstate.stack.append(global_state.environment.gasprice)
        return [global_state]

    @StateTransition()
    def basefee_(self, global_state: GlobalState) -> List[GlobalState]:
        """

        :param global_state:
        :return:
        """
        global_state.mstate.stack.append(global_state.environment.basefee)
        return [global_state]

    @StateTransition()
    def codecopy_(self, global_state: GlobalState) -> List[GlobalState]:
        """

        :param global_state:
        :return:
        """
        memory_offset, code_offset, size = (
            global_state.mstate.stack.pop(),
            global_state.mstate.stack.pop(),
            global_state.mstate.stack.pop(),
        )
        code = global_state.environment.code.bytecode
        if code[0:2] == "0x":
            code = code[2:]
        code_size = len(code) // 2
        if isinstance(global_state.current_transaction, ContractCreationTransaction):
            # Treat creation code after the expected disassembly as calldata.
            # This is a slightly hacky way to ensure that symbolic constructor
            # arguments work correctly.
            mstate = global_state.mstate
            offset = code_offset - code_size
            log.debug("Copying from code offset: {} with size: {}".format(offset, size))

            if isinstance(global_state.environment.calldata, SymbolicCalldata):
                if code_offset >= code_size:
                    return self._calldata_copy_helper(
                        global_state, mstate, memory_offset, offset, size
                    )
            else:
                # Copy from both code and calldata appropriately.
                concrete_code_offset = helper.get_concrete_int(code_offset)
                concrete_size = helper.get_concrete_int(size)

                code_copy_offset = concrete_code_offset
                code_copy_size = (
                    concrete_size
                    if concrete_code_offset + concrete_size <= code_size
                    else code_size - concrete_code_offset
                )
                code_copy_size = code_copy_size if code_copy_size >= 0 else 0

                calldata_copy_offset = (
                    concrete_code_offset - code_size
                    if concrete_code_offset - code_size > 0
                    else 0
                )
                calldata_copy_size = concrete_code_offset + concrete_size - code_size
                calldata_copy_size = (
                    calldata_copy_size if calldata_copy_size >= 0 else 0
                )

                [global_state] = self._code_copy_helper(
                    code=global_state.environment.code.bytecode,
                    memory_offset=memory_offset,
                    code_offset=code_copy_offset,
                    size=code_copy_size,
                    op="CODECOPY",
                    global_state=global_state,
                )
                return self._calldata_copy_helper(
                    global_state=global_state,
                    mstate=mstate,
                    mstart=memory_offset + code_copy_size,
                    dstart=calldata_copy_offset,
                    size=calldata_copy_size,
                )

        return self._code_copy_helper(
            code=global_state.environment.code.bytecode,
            memory_offset=memory_offset,
            code_offset=code_offset,
            size=size,
            op="CODECOPY",
            global_state=global_state,
        )

    @StateTransition()
    def extcodesize_(self, global_state: GlobalState) -> List[GlobalState]:
        """

        :param global_state:
        :return:
        """
        state = global_state.mstate
        addr = state.stack.pop()
        try:
            addr = hex(helper.get_concrete_int(addr))
        except TypeError:
            log.debug("unsupported symbolic address for EXTCODESIZE")
            state.stack.append(global_state.new_bitvec("extcodesize_" + str(addr), 256))
            return [global_state]
        try:
            code = global_state.world_state.accounts_exist_or_load(
                addr, self.dynamic_loader
            ).code.bytecode
        except (ValueError, AttributeError) as e:
            log.debug("error accessing contract storage due to: " + str(e))
            state.stack.append(global_state.new_bitvec("extcodesize_" + str(addr), 256))
            return [global_state]

        state.stack.append(len(code) // 2)

        return [global_state]

    @staticmethod
    def _code_copy_helper(
        code: Union[str, Tuple],
        memory_offset: Union[int, BitVec],
        code_offset: Union[int, BitVec],
        size: Union[int, BitVec],
        op: str,
        global_state: GlobalState,
    ) -> List[GlobalState]:
        try:
            concrete_memory_offset = helper.get_concrete_int(memory_offset)
        except TypeError:
            log.debug("Unsupported symbolic memory offset in {}".format(op))
            return [global_state]

        try:
            concrete_size = helper.get_concrete_int(size)
            global_state.mstate.mem_extend(concrete_memory_offset, concrete_size)

        except TypeError:
            # except both attribute error and Exception
            global_state.mstate.mem_extend(concrete_memory_offset, 1)
            global_state.mstate.memory[
                concrete_memory_offset
            ] = global_state.new_bitvec(
                "code({})".format(
                    global_state.environment.active_account.contract_name
                ),
                8,
            )
            return [global_state]

        try:
            concrete_code_offset = helper.get_concrete_int(code_offset)
        except TypeError:
            log.debug("Unsupported symbolic code offset in {}".format(op))
            global_state.mstate.mem_extend(concrete_memory_offset, concrete_size)
            for i in range(concrete_size):
                global_state.mstate.memory[
                    concrete_memory_offset + i
                ] = global_state.new_bitvec(
                    "code({})".format(
                        global_state.environment.active_account.contract_name
                    ),
                    8,
                )
            return [global_state]

        if code[0:2] == "0x":
            code = code[2:]

        for i in range(concrete_size):
            if isinstance(code, str):
                if 2 * (concrete_code_offset + i + 1) > len(code):
                    break

                global_state.mstate.memory[concrete_memory_offset + i] = int(
                    code[
                        2
                        * (concrete_code_offset + i) : 2
                        * (concrete_code_offset + i + 1)
                    ],
                    16,
                )
            else:
                if (concrete_code_offset + i + 1) > len(code):
                    break

                global_state.mstate.memory[concrete_memory_offset + i] = code[
                    concrete_code_offset + i
                ]

        return [global_state]

    @StateTransition()
    def extcodecopy_(self, global_state: GlobalState) -> List[GlobalState]:
        """

        :param global_state:
        :return:
        """
        state = global_state.mstate
        addr, memory_offset, code_offset, size = (
            state.stack.pop(),
            state.stack.pop(),
            state.stack.pop(),
            state.stack.pop(),
        )
        try:
            addr = hex(helper.get_concrete_int(addr))
        except TypeError:
            log.debug("unsupported symbolic address for EXTCODECOPY")
            return [global_state]

        try:
            code = global_state.world_state.accounts_exist_or_load(
                addr, self.dynamic_loader
            ).code.bytecode
        except (ValueError, AttributeError) as e:
            log.debug("error accessing contract storage due to: " + str(e))
            return [global_state]

        return self._code_copy_helper(
            code=code,
            memory_offset=memory_offset,
            code_offset=code_offset,
            size=size,
            op="EXTCODECOPY",
            global_state=global_state,
        )

    @StateTransition()
    def extcodehash_(self, global_state: GlobalState) -> List[GlobalState]:
        """

        :param global_state:
        :return: List of global states possible, list of size 1 in this case
        """
        world_state = global_state.world_state
        stack = global_state.mstate.stack
        address = Extract(159, 0, stack.pop())

        if address.symbolic:
            code_hash = symbol_factory.BitVecVal(int(get_code_hash(""), 16), 256)
        elif address.value not in world_state.accounts:
            code_hash = symbol_factory.BitVecVal(0, 256)
        else:
            addr = "0" * (40 - len(hex(address.value)[2:])) + hex(address.value)[2:]
            code = world_state.accounts_exist_or_load(
                addr, self.dynamic_loader
            ).code.bytecode
            code_hash = symbol_factory.BitVecVal(int(get_code_hash(code), 16), 256)
        stack.append(code_hash)
        return [global_state]

    @StateTransition()
    def returndatacopy_(self, global_state: GlobalState) -> List[GlobalState]:
        """

        :param global_state:
        :return:
        """
        state = global_state.mstate
        memory_offset, return_offset, size = (
            state.stack.pop(),
            state.stack.pop(),
            state.stack.pop(),
        )

        try:
            concrete_memory_offset = helper.get_concrete_int(memory_offset)
        except TypeError:
            log.debug("Unsupported symbolic memory offset in RETURNDATACOPY")
            return [global_state]

        try:
            concrete_return_offset = helper.get_concrete_int(return_offset)
        except TypeError:
            log.debug("Unsupported symbolic return offset in RETURNDATACOPY")
            return [global_state]

        try:
            concrete_size = helper.get_concrete_int(size)
        except TypeError:
            log.debug("Unsupported symbolic max_length offset in RETURNDATACOPY")
            return [global_state]

        if global_state.last_return_data is None:
            return [global_state]

        global_state.mstate.mem_extend(concrete_memory_offset, concrete_size)
        for i in range(concrete_size):
            global_state.mstate.memory[concrete_memory_offset + i] = (
                global_state.last_return_data[concrete_return_offset + i]
                if i < len(global_state.last_return_data)
                else 0
            )

        return [global_state]

    @StateTransition()
    def returndatasize_(self, global_state: GlobalState) -> List[GlobalState]:
        """

        :param global_state:
        :return:
        """
        if global_state.last_return_data is None:
            log.debug(
                "No last_return_data found, adding an unconstrained bitvec to the stack"
            )
            global_state.mstate.stack.append(
                global_state.new_bitvec("returndatasize", 256)
            )
        else:
            global_state.mstate.stack.append(len(global_state.last_return_data))

        return [global_state]

    @StateTransition()
    def blockhash_(self, global_state: GlobalState) -> List[GlobalState]:
        """

        :param global_state:
        :return:
        """
        state = global_state.mstate
        blocknumber = state.stack.pop()
        state.stack.append(
            global_state.new_bitvec("blockhash_block_" + str(blocknumber), 256)
        )
        return [global_state]

    @StateTransition()
    def coinbase_(self, global_state: GlobalState) -> List[GlobalState]:
        """

        :param global_state:
        :return:
        """
        global_state.mstate.stack.append(global_state.new_bitvec("coinbase", 256))
        return [global_state]

    @StateTransition()
    def timestamp_(self, global_state: GlobalState) -> List[GlobalState]:
        """

        :param global_state:
        :return:
        """
        global_state.mstate.stack.append(global_state.new_bitvec("timestamp", 256))
        return [global_state]

    @StateTransition()
    def number_(self, global_state: GlobalState) -> List[GlobalState]:
        """

        :param global_state:
        :return:
        """
        global_state.mstate.stack.append(global_state.environment.block_number)
        return [global_state]

    @StateTransition()
    def difficulty_(self, global_state: GlobalState) -> List[GlobalState]:
        """

        :param global_state:
        :return:
        """
        global_state.mstate.stack.append(
            global_state.new_bitvec("block_difficulty", 256)
        )
        return [global_state]

    @StateTransition()
    def gaslimit_(self, global_state: GlobalState) -> List[GlobalState]:
        """

        :param global_state:
        :return:
        """
        global_state.mstate.stack.append(global_state.mstate.gas_limit)
        return [global_state]

    # Memory operations
    @StateTransition()
    def mload_(self, global_state: GlobalState) -> List[GlobalState]:
        """

        :param global_state:
        :return:
        """
        state = global_state.mstate
        offset = state.stack.pop()

        state.mem_extend(offset, 32)
        data = state.memory.get_word_at(offset)
        state.stack.append(data)
        return [global_state]

    @StateTransition()
    def mstore_(self, global_state: GlobalState) -> List[GlobalState]:
        """

        :param global_state:
        :return:
        """
        state = global_state.mstate
        mstart, value = state.stack.pop(), state.stack.pop()

        try:
            state.mem_extend(mstart, 32)
        except Exception:
            log.debug("Error extending memory")

        state.memory.write_word_at(mstart, value)

        return [global_state]

    @StateTransition()
    def mstore8_(self, global_state: GlobalState) -> List[GlobalState]:
        """

        :param global_state:
        :return:
        """
        state = global_state.mstate
        offset, value = state.stack.pop(), state.stack.pop()

        state.mem_extend(offset, 1)

        try:
            value_to_write = (
                util.get_concrete_int(value) % 256
            )  # type: Union[int, BitVec]
        except TypeError:  # BitVec
            value_to_write = Extract(7, 0, value)

        state.memory[offset] = value_to_write

        return [global_state]

    @StateTransition()
    def sload_(self, global_state: GlobalState) -> List[GlobalState]:
        """

        :param global_state:
        :return:
        """

        state = global_state.mstate
        index = state.stack.pop()
        state.stack.append(global_state.environment.active_account.storage[index])
        return [global_state]

    @StateTransition(is_state_mutation_instruction=True)
    def sstore_(self, global_state: GlobalState) -> List[GlobalState]:
        """

        :param global_state:
        :return:
        """
        state = global_state.mstate
        index, value = state.stack.pop(), state.stack.pop()
        global_state.environment.active_account.storage[index] = value
        return [global_state]

    @StateTransition(increment_pc=False, enable_gas=False)
    def jump_(self, global_state: GlobalState) -> List[GlobalState]:
        """

        :param global_state:
        :return:
        """
        state = global_state.mstate
        disassembly = global_state.environment.code
        try:
            jump_addr = util.get_concrete_int(state.stack.pop())
        except TypeError:
            raise InvalidJumpDestination("Invalid jump argument (symbolic address)")
        except IndexError:
            raise StackUnderflowException()

        index = util.get_instruction_index(disassembly.instruction_list, jump_addr)
        if index is None:
            raise InvalidJumpDestination("JUMP to invalid address")

        op_code = disassembly.instruction_list[index]["opcode"]

        if op_code != "JUMPDEST":
            raise InvalidJumpDestination(
                "Skipping JUMP to invalid destination (not JUMPDEST): " + str(jump_addr)
            )

        new_state = copy(global_state)
        # add JUMP gas cost
        min_gas, max_gas = get_opcode_gas("JUMP")
        new_state.mstate.min_gas_used += min_gas
        new_state.mstate.max_gas_used += max_gas

        # manually set PC to destination
        new_state.mstate.pc = index
        new_state.mstate.depth += 1

        return [new_state]

    @StateTransition(increment_pc=False, enable_gas=False)
    def jumpi_(self, global_state: GlobalState) -> List[GlobalState]:
        """

        :param global_state:
        :return:
        """
        state = global_state.mstate
        disassembly = global_state.environment.code
        min_gas, max_gas = get_opcode_gas("JUMPI")
        states = []

        op0, condition = state.stack.pop(), state.stack.pop()

        try:
            jump_addr = util.get_concrete_int(op0)
        except TypeError:
            log.debug("Skipping JUMPI to invalid destination.")
            global_state.mstate.pc += 1
            global_state.mstate.min_gas_used += min_gas
            global_state.mstate.max_gas_used += max_gas
            return [global_state]

        # False case
        negated = (
            simplify(Not(condition)) if isinstance(condition, Bool) else condition == 0
        )
        negated.simplify()
        # True case
        condi = simplify(condition) if isinstance(condition, Bool) else condition != 0
        condi.simplify()

        negated_cond = (type(negated) == bool and negated) or (
            isinstance(negated, Bool) and not is_false(negated)
        )
        positive_cond = (type(condi) == bool and condi) or (
            isinstance(condi, Bool) and not is_false(condi)
        )

        if negated_cond:
            new_state = copy(global_state)
            # add JUMPI gas cost
            new_state.mstate.min_gas_used += min_gas
            new_state.mstate.max_gas_used += max_gas

            # manually increment PC
            new_state.mstate.depth += 1
            new_state.mstate.pc += 1
            new_state.world_state.constraints.append(negated)
            states.append(new_state)
        else:
            log.debug("Pruned unreachable states.")

        # True case

        # Get jump destination
        index = util.get_instruction_index(disassembly.instruction_list, jump_addr)

        if index is None:
            log.debug("Invalid jump destination: " + str(jump_addr))
            return states

        instr = disassembly.instruction_list[index]

        if instr["opcode"] == "JUMPDEST":
            if positive_cond:
                new_state = copy(global_state)
                # add JUMPI gas cost
                new_state.mstate.min_gas_used += min_gas
                new_state.mstate.max_gas_used += max_gas

                # manually set PC to destination
                new_state.mstate.pc = index
                new_state.mstate.depth += 1
                new_state.world_state.constraints.append(condi)
                states.append(new_state)
            else:
                log.debug("Pruned unreachable states.")
        return states

    @StateTransition()
    def beginsub_(self, global_state: GlobalState) -> List[GlobalState]:
        """
        This opcode depicts the start of the subroutine
        """
        raise OutOfGasException("Encountered BEGINSUB")

    @StateTransition()
    def jumpsub_(self, global_state: GlobalState) -> List[GlobalState]:
        """
        Jump to the subroutine
        """
        disassembly = global_state.environment.code
        try:
            location = util.get_concrete_int(global_state.mstate.stack.pop())
        except TypeError:
            raise VmException("Encountered symbolic JUMPSUB location")
        index = util.get_instruction_index(disassembly.instruction_list, location)
        instr = disassembly.instruction_list[index]

        if instr["opcode"] != "BEGINSUB":
            raise VmException(
                "Encountered invalid JUMPSUB location :{}".format(instr["address"])
            )
        global_state.mstate.subroutine_stack.append(global_state.mstate.pc + 1)
        global_state.mstate.pc = location
        return [global_state]

    @StateTransition(increment_pc=False)
    def returnsub_(self, global_state: GlobalState) -> List[GlobalState]:
        """
        Returns control to the caller of the subroutine
        """
        global_state.mstate.pc = global_state.mstate.subroutine_stack.pop()
        return [global_state]

    @StateTransition()
    def pc_(self, global_state: GlobalState) -> List[GlobalState]:
        """

        :param global_state:
        :return:
        """
        index = global_state.mstate.pc
        program_counter = global_state.environment.code.instruction_list[index][
            "address"
        ]
        global_state.mstate.stack.append(symbol_factory.BitVecVal(program_counter, 256))

        return [global_state]

    @StateTransition()
    def msize_(self, global_state: GlobalState) -> List[GlobalState]:
        """

        :param global_state:
        :return:
        """
        global_state.mstate.stack.append(global_state.mstate.memory_size)
        return [global_state]

    @StateTransition()
    def gas_(self, global_state: GlobalState) -> List[GlobalState]:
        """

        :param global_state:
        :return:
        """
        # TODO: Push a Constrained variable which lies between min gas and max gas
        global_state.mstate.stack.append(global_state.new_bitvec("gas", 256))
        return [global_state]

    @StateTransition(is_state_mutation_instruction=True)
    def log_(self, global_state: GlobalState) -> List[GlobalState]:
        """

        :param global_state:
        :return:
        """
        # TODO: implement me
        state = global_state.mstate
        depth = int(self.op_code[3:])
        state.stack.pop(), state.stack.pop()
        _ = [state.stack.pop() for _ in range(depth)]
        # Not supported
        return [global_state]

    def _create_transaction_helper(
        self, global_state, call_value, mem_offset, mem_size, create2_salt=None
    ) -> List[GlobalState]:
        mstate = global_state.mstate
        environment = global_state.environment
        world_state = global_state.world_state

        call_data = get_call_data(global_state, mem_offset, mem_offset + mem_size)
        code_raw = []
        code_end = call_data.size
        size = call_data.size
        if isinstance(size, BitVec):
            # Other size restriction checks handle this
            if size.symbolic:
                size = 10 ** 5
            else:
                size = size.value
        for i in range(size):
            if call_data[i].symbolic:
                code_end = i
                break
            code_raw.append(call_data[i].value)

        if len(code_raw) < 1:
            global_state.mstate.stack.append(1)
            log.debug("No code found for trying to execute a create type instruction.")
            return [global_state]

        code_str = bytes.hex(bytes(code_raw))

        next_transaction_id = get_next_transaction_id()
        constructor_arguments = ConcreteCalldata(
            next_transaction_id, call_data[code_end:]
        )
        code = Disassembly(code_str)

        caller = environment.active_account.address
        gas_price = environment.gasprice
        origin = environment.origin

        contract_address = None  # type: Union[BitVec, int]
        Instruction._sha3_gas_helper(global_state, len(code_str[2:]) // 2)

        if create2_salt:
            if create2_salt.symbolic:
                if create2_salt.size() != 256:
                    pad = symbol_factory.BitVecVal(0, 256 - create2_salt.size())
                    create2_salt = Concat(pad, create2_salt)
                address = keccak_function_manager.create_keccak(
                    Concat(
                        symbol_factory.BitVecVal(255, 8),
                        caller,
                        create2_salt,
                        symbol_factory.BitVecVal(int(get_code_hash(code_str), 16), 256),
                    )
                )
                contract_address = Extract(255, 96, address)

            else:
                salt = hex(create2_salt.value)[2:]
                salt = "0" * (64 - len(salt)) + salt

                addr = hex(caller.value)[2:]
                addr = "0" * (40 - len(addr)) + addr

                contract_address = int(
                    get_code_hash("0xff" + addr + salt + get_code_hash(code_str)[2:])[
                        26:
                    ],
                    16,
                )
        transaction = ContractCreationTransaction(
            world_state=world_state,
            caller=caller,
            code=code,
            call_data=constructor_arguments,
            gas_price=gas_price,
            gas_limit=mstate.gas_limit,
            origin=origin,
            call_value=call_value,
            contract_address=contract_address,
        )
        raise TransactionStartSignal(transaction, self.op_code, global_state)

    @StateTransition(is_state_mutation_instruction=True)
    def create_(self, global_state: GlobalState) -> List[GlobalState]:
        """

        :param global_state:
        :return:
        """
        call_value, mem_offset, mem_size = global_state.mstate.pop(3)
        return self._create_transaction_helper(
            global_state, call_value, mem_offset, mem_size
        )

    @StateTransition()
    def create_post(self, global_state: GlobalState) -> List[GlobalState]:
        return self._handle_create_type_post(global_state)

    @StateTransition(is_state_mutation_instruction=True)
    def create2_(self, global_state: GlobalState) -> List[GlobalState]:
        """

        :param global_state:
        :return:
        """
        call_value, mem_offset, mem_size, salt = global_state.mstate.pop(4)

        return self._create_transaction_helper(
            global_state, call_value, mem_offset, mem_size, salt
        )

    @StateTransition()
    def create2_post(self, global_state: GlobalState) -> List[GlobalState]:
        return self._handle_create_type_post(global_state, opcode="create2")

    @staticmethod
    def _handle_create_type_post(global_state, opcode="create"):
        if opcode == "create2":
            global_state.mstate.pop(4)
        else:
            global_state.mstate.pop(3)
        if global_state.last_return_data:
            return_val = symbol_factory.BitVecVal(
                int(global_state.last_return_data, 16), 256
            )
        else:
            return_val = symbol_factory.BitVecVal(0, 256)
        global_state.mstate.stack.append(return_val)
        return [global_state]

    @StateTransition()
    def return_(self, global_state: GlobalState):
        """

        :param global_state:
        """
        state = global_state.mstate
        offset, length = state.stack.pop(), state.stack.pop()
        if length.symbolic:
            return_data = [global_state.new_bitvec("return_data", 8)]
            log.debug("Return with symbolic length or offset. Not supported")
        else:
            state.mem_extend(offset, length)
            StateTransition.check_gas_usage_limit(global_state)
            return_data = state.memory[offset : offset + length]
        global_state.current_transaction.end(global_state, return_data)

    @StateTransition(is_state_mutation_instruction=True)
    def selfdestruct_(self, global_state: GlobalState):
        """

        :param global_state:
        """
        target = global_state.mstate.stack.pop()
        transfer_amount = global_state.environment.active_account.balance()
        # Often the target of the selfdestruct instruction will be symbolic
        # If it isn't then we'll transfer the balance to the indicated contract
        global_state.world_state.balances[target] += transfer_amount

        global_state.environment.active_account = deepcopy(
            global_state.environment.active_account
        )
        global_state.accounts[
            global_state.environment.active_account.address.value
        ] = global_state.environment.active_account

        global_state.environment.active_account.set_balance(0)
        global_state.environment.active_account.deleted = True
        global_state.current_transaction.end(global_state)

    @StateTransition()
    def revert_(self, global_state: GlobalState) -> None:
        """

        :param global_state:
        """
        state = global_state.mstate
        offset, length = state.stack.pop(), state.stack.pop()
        return_data = [global_state.new_bitvec("return_data", 8)]
        try:
            return_data = state.memory[
                util.get_concrete_int(offset) : util.get_concrete_int(offset + length)
            ]
        except TypeError:
            log.debug("Return with symbolic length or offset. Not supported")
        global_state.current_transaction.end(
            global_state, return_data=return_data, revert=True
        )

    @StateTransition()
    def assert_fail_(self, global_state: GlobalState):
        """

        :param global_state:
        """
        # 0xfe: designated invalid opcode
        raise InvalidInstruction

    @StateTransition()
    def invalid_(self, global_state: GlobalState):
        """

        :param global_state:
        """
        raise InvalidInstruction

    @StateTransition()
    def stop_(self, global_state: GlobalState):
        """

        :param global_state:
        """
        global_state.current_transaction.end(global_state)

    @staticmethod
    def _write_symbolic_returndata(
        global_state: GlobalState, memory_out_offset: BitVec, memory_out_size: BitVec
    ):
        """
        Writes symbolic return-data into memory, The memory offset and size should be concrete
        :param global_state:
        :param memory_out_offset:
        :param memory_out_size:
        :return:
        """
        if memory_out_offset.symbolic is True or memory_out_size.symbolic is True:
            return
        for i in range(memory_out_size.value):
            global_state.mstate.memory[memory_out_offset + i] = global_state.new_bitvec(
                "call_output_var({})_{}".format(
                    simplify(memory_out_offset + i), global_state.mstate.pc
                ),
                8,
            )

    @StateTransition()
    def call_(self, global_state: GlobalState) -> List[GlobalState]:
        """

        :param global_state:
        :return:
        """
        instr = global_state.get_current_instruction()
        environment = global_state.environment

        memory_out_size, memory_out_offset = global_state.mstate.stack[-7:-5]
        try:
            (
                callee_address,
                callee_account,
                call_data,
                value,
                gas,
                memory_out_offset,
                memory_out_size,
            ) = get_call_parameters(global_state, self.dynamic_loader, True)

            if callee_account is not None and callee_account.code.bytecode == "":
                log.debug("The call is related to ether transfer between accounts")
                sender = environment.active_account.address
                receiver = callee_account.address
                transfer_ether(global_state, sender, receiver, value)

                global_state.mstate.stack.append(
                    global_state.new_bitvec("retval_" + str(instr["address"]), 256)
                )
                return [global_state]

        except ValueError as e:
            log.debug(
                "Could not determine required parameters for call, putting fresh symbol on the stack. \n{}".format(
                    e
                )
            )
            self._write_symbolic_returndata(
                global_state, memory_out_offset, memory_out_size
            )
            # TODO: decide what to do in this case
            global_state.mstate.stack.append(
                global_state.new_bitvec("retval_" + str(instr["address"]), 256)
            )
            return [global_state]

        if environment.static:
            if isinstance(value, int) and value > 0:
                raise WriteProtection(
                    "Cannot call with non zero value in a static call"
                )
            if isinstance(value, BitVec):
                if value.symbolic:
                    global_state.world_state.constraints.append(
                        value == symbol_factory.BitVecVal(0, 256)
                    )
                elif value.value > 0:
                    raise WriteProtection(
                        "Cannot call with non zero value in a static call"
                    )

        native_result = native_call(
            global_state, callee_address, call_data, memory_out_offset, memory_out_size
        )
        if native_result:
            return native_result
        transaction = MessageCallTransaction(
            world_state=global_state.world_state,
            gas_price=environment.gasprice,
            gas_limit=gas,
            origin=environment.origin,
            caller=environment.active_account.address,
            callee_account=callee_account,
            call_data=call_data,
            call_value=value,
            static=environment.static,
        )
        raise TransactionStartSignal(transaction, self.op_code, global_state)

    @StateTransition()
    def call_post(self, global_state: GlobalState) -> List[GlobalState]:
        """

        :param global_state:
        :return:
        """

        return self.post_handler(global_state, function_name="call")

    @StateTransition()
    def callcode_(self, global_state: GlobalState) -> List[GlobalState]:
        """

        :param global_state:
        :return:
        """
        instr = global_state.get_current_instruction()
        environment = global_state.environment
        memory_out_size, memory_out_offset = global_state.mstate.stack[-7:-5]
        try:
            (
                callee_address,
                callee_account,
                call_data,
                value,
                gas,
                _,
                _,
            ) = get_call_parameters(global_state, self.dynamic_loader, True)

            if callee_account is not None and callee_account.code.bytecode == "":
                log.debug("The call is related to ether transfer between accounts")
                sender = global_state.environment.active_account.address
                receiver = callee_account.address
                transfer_ether(global_state, sender, receiver, value)

                global_state.mstate.stack.append(
                    global_state.new_bitvec("retval_" + str(instr["address"]), 256)
                )
                return [global_state]

        except ValueError as e:
            log.debug(
                "Could not determine required parameters for call, putting fresh symbol on the stack. \n{}".format(
                    e
                )
            )
            self._write_symbolic_returndata(
                global_state, memory_out_offset, memory_out_size
            )
            global_state.mstate.stack.append(
                global_state.new_bitvec("retval_" + str(instr["address"]), 256)
            )
            return [global_state]

        native_result = native_call(
            global_state, callee_address, call_data, memory_out_offset, memory_out_size
        )
        if native_result:
            return native_result

        transaction = MessageCallTransaction(
            world_state=global_state.world_state,
            gas_price=environment.gasprice,
            gas_limit=gas,
            origin=environment.origin,
            code=callee_account.code,
            caller=environment.address,
            callee_account=environment.active_account,
            call_data=call_data,
            call_value=value,
            static=environment.static,
        )
        raise TransactionStartSignal(transaction, self.op_code, global_state)

    @StateTransition()
    def callcode_post(self, global_state: GlobalState) -> List[GlobalState]:
        """

        :param global_state:
        :return:
        """
        instr = global_state.get_current_instruction()
        memory_out_size, memory_out_offset = global_state.mstate.stack[-7:-5]
        try:
            (
                _,
                _,
                _,
                _,
                _,
                memory_out_offset,
                memory_out_size,
            ) = get_call_parameters(global_state, self.dynamic_loader, True)
        except ValueError as e:
            log.debug(
                "Could not determine required parameters for call, putting fresh symbol on the stack. \n{}".format(
                    e
                )
            )
            self._write_symbolic_returndata(
                global_state, memory_out_offset, memory_out_size
            )
            global_state.mstate.stack.append(
                global_state.new_bitvec("retval_" + str(instr["address"]), 256)
            )
            return [global_state]

        if global_state.last_return_data is None:
            # Put return value on stack
            return_value = global_state.new_bitvec(
                "retval_" + str(instr["address"]), 256
            )
            global_state.mstate.stack.append(return_value)
            self._write_symbolic_returndata(
                global_state, memory_out_offset, memory_out_size
            )
            global_state.world_state.constraints.append(return_value == 0)
            return [global_state]

        try:
            memory_out_offset = (
                util.get_concrete_int(memory_out_offset)
                if isinstance(memory_out_offset, Expression)
                else memory_out_offset
            )
            memory_out_size = (
                util.get_concrete_int(memory_out_size)
                if isinstance(memory_out_size, Expression)
                else memory_out_size
            )
        except TypeError:
            global_state.mstate.stack.append(
                global_state.new_bitvec("retval_" + str(instr["address"]), 256)
            )
            return [global_state]

        # Copy memory
        global_state.mstate.mem_extend(
            memory_out_offset, min(memory_out_size, len(global_state.last_return_data))
        )
        for i in range(min(memory_out_size, len(global_state.last_return_data))):
            global_state.mstate.memory[
                i + memory_out_offset
            ] = global_state.last_return_data[i]

        # Put return value on stack
        return_value = global_state.new_bitvec("retval_" + str(instr["address"]), 256)
        global_state.mstate.stack.append(return_value)
        global_state.world_state.constraints.append(return_value == 1)
        return [global_state]

    @StateTransition()
    def delegatecall_(self, global_state: GlobalState) -> List[GlobalState]:
        """

        :param global_state:
        :return:
        """
        instr = global_state.get_current_instruction()
        environment = global_state.environment
        memory_out_size, memory_out_offset = global_state.mstate.stack[-6:-4]

        try:
            (
                callee_address,
                callee_account,
                call_data,
                value,
                gas,
                _,
                _,
            ) = get_call_parameters(global_state, self.dynamic_loader)

            if callee_account is not None and callee_account.code.bytecode == "":
                log.debug("The call is related to ether transfer between accounts")
                sender = global_state.environment.active_account.address
                receiver = callee_account.address
                transfer_ether(global_state, sender, receiver, value)

                global_state.mstate.stack.append(
                    global_state.new_bitvec("retval_" + str(instr["address"]), 256)
                )
                return [global_state]
        except ValueError as e:
            log.debug(
                "Could not determine required parameters for call, putting fresh symbol on the stack. \n{}".format(
                    e
                )
            )
            self._write_symbolic_returndata(
                global_state, memory_out_offset, memory_out_size
            )
            global_state.mstate.stack.append(
                global_state.new_bitvec("retval_" + str(instr["address"]), 256)
            )
            return [global_state]

        native_result = native_call(
            global_state, callee_address, call_data, memory_out_offset, memory_out_size
        )
        if native_result:
            return native_result

        transaction = MessageCallTransaction(
            world_state=global_state.world_state,
            gas_price=environment.gasprice,
            gas_limit=gas,
            origin=environment.origin,
            code=callee_account.code,
            caller=environment.sender,
            callee_account=environment.active_account,
            call_data=call_data,
            call_value=environment.callvalue,
            static=environment.static,
        )
        raise TransactionStartSignal(transaction, self.op_code, global_state)

    @StateTransition()
    def delegatecall_post(self, global_state: GlobalState) -> List[GlobalState]:
        """

        :param global_state:
        :return:
        """
        instr = global_state.get_current_instruction()
        memory_out_size, memory_out_offset = global_state.mstate.stack[-6:-4]

        try:
            (
                _,
                _,
                _,
                _,
                _,
                memory_out_offset,
                memory_out_size,
            ) = get_call_parameters(global_state, self.dynamic_loader)
        except ValueError as e:
            log.debug(
                "Could not determine required parameters for call, putting fresh symbol on the stack. \n{}".format(
                    e
                )
            )
            global_state.mstate.stack.append(
                global_state.new_bitvec("retval_" + str(instr["address"]), 256)
            )
            self._write_symbolic_returndata(
                global_state, memory_out_offset, memory_out_size
            )
            return [global_state]

        if global_state.last_return_data is None:
            # Put return value on stack
            return_value = global_state.new_bitvec(
                "retval_" + str(instr["address"]), 256
            )
            global_state.mstate.stack.append(return_value)
            global_state.world_state.constraints.append(return_value == 0)
            return [global_state]

        try:
            memory_out_offset = (
                util.get_concrete_int(memory_out_offset)
                if isinstance(memory_out_offset, Expression)
                else memory_out_offset
            )
            memory_out_size = (
                util.get_concrete_int(memory_out_size)
                if isinstance(memory_out_size, Expression)
                else memory_out_size
            )
        except TypeError:
            global_state.mstate.stack.append(
                global_state.new_bitvec("retval_" + str(instr["address"]), 256)
            )
            return [global_state]

            # Copy memory
        global_state.mstate.mem_extend(
            memory_out_offset, min(memory_out_size, len(global_state.last_return_data))
        )
        for i in range(min(memory_out_size, len(global_state.last_return_data))):
            global_state.mstate.memory[
                i + memory_out_offset
            ] = global_state.last_return_data[i]

        # Put return value on stack
        return_value = global_state.new_bitvec("retval_" + str(instr["address"]), 256)
        global_state.mstate.stack.append(return_value)
        global_state.world_state.constraints.append(return_value == 1)
        return [global_state]

    @StateTransition()
    def staticcall_(self, global_state: GlobalState) -> List[GlobalState]:
        """

        :param global_state:
        :return:
        """
        instr = global_state.get_current_instruction()
        environment = global_state.environment
        memory_out_size, memory_out_offset = global_state.mstate.stack[-6:-4]
        try:
            (
                callee_address,
                callee_account,
                call_data,
                value,
                gas,
                memory_out_offset,
                memory_out_size,
            ) = get_call_parameters(global_state, self.dynamic_loader)

            if callee_account is not None and callee_account.code.bytecode == "":
                log.debug("The call is related to ether transfer between accounts")
                sender = environment.active_account.address
                receiver = callee_account.address
                transfer_ether(global_state, sender, receiver, value)

                global_state.mstate.stack.append(
                    global_state.new_bitvec("retval_" + str(instr["address"]), 256)
                )
                return [global_state]

        except ValueError as e:
            log.debug(
                "Could not determine required parameters for call, putting fresh symbol on the stack. \n{}".format(
                    e
                )
            )
            self._write_symbolic_returndata(
                global_state, memory_out_offset, memory_out_size
            )
            global_state.mstate.stack.append(
                global_state.new_bitvec("retval_" + str(instr["address"]), 256)
            )
            return [global_state]

        native_result = native_call(
            global_state, callee_address, call_data, memory_out_offset, memory_out_size
        )

        if native_result:
            return native_result

        transaction = MessageCallTransaction(
            world_state=global_state.world_state,
            gas_price=environment.gasprice,
            gas_limit=gas,
            origin=environment.origin,
            code=callee_account.code,
            caller=environment.address,
            callee_account=callee_account,
            call_data=call_data,
            call_value=value,
            static=True,
        )
        raise TransactionStartSignal(transaction, self.op_code, global_state)

    @StateTransition()
    def staticcall_post(self, global_state: GlobalState) -> List[GlobalState]:
        return self.post_handler(global_state, function_name="staticcall")

    def post_handler(self, global_state, function_name: str):
        instr = global_state.get_current_instruction()
        if function_name in ("staticcall", "delegatecall"):
            memory_out_size, memory_out_offset = global_state.mstate.stack[-6:-4]
        else:
            memory_out_size, memory_out_offset = global_state.mstate.stack[-7:-5]

        try:
            with_value = function_name != "staticcall"
            (
                _,
                _,
                _,
                _,
                _,
                memory_out_offset,
                memory_out_size,
            ) = get_call_parameters(global_state, self.dynamic_loader, with_value)
        except ValueError as e:
            log.debug(
                "Could not determine required parameters for {}, putting fresh symbol on the stack. \n{}".format(
                    function_name, e
                )
            )
            self._write_symbolic_returndata(
                global_state, memory_out_offset, memory_out_size
            )
            global_state.mstate.stack.append(
                global_state.new_bitvec("retval_" + str(instr["address"]), 256)
            )
            return [global_state]

        if global_state.last_return_data is None:
            # Put return value on stack
            return_value = global_state.new_bitvec(
                "retval_" + str(instr["address"]), 256
            )
            global_state.mstate.stack.append(return_value)
            return [global_state]

        try:
            memory_out_offset = (
                util.get_concrete_int(memory_out_offset)
                if isinstance(memory_out_offset, Expression)
                else memory_out_offset
            )
            memory_out_size = (
                util.get_concrete_int(memory_out_size)
                if isinstance(memory_out_size, Expression)
                else memory_out_size
            )
        except TypeError:
            global_state.mstate.stack.append(
                global_state.new_bitvec("retval_" + str(instr["address"]), 256)
            )
            return [global_state]

        # Copy memory
        global_state.mstate.mem_extend(
            memory_out_offset, min(memory_out_size, len(global_state.last_return_data))
        )
        for i in range(min(memory_out_size, len(global_state.last_return_data))):
            global_state.mstate.memory[
                i + memory_out_offset
            ] = global_state.last_return_data[i]

        # Put return value on stack
        return_value = global_state.new_bitvec("retval_" + str(instr["address"]), 256)
        global_state.mstate.stack.append(return_value)
        global_state.world_state.constraints.append(return_value == 1)

        return [global_state]
