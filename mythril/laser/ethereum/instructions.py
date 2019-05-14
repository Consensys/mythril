"""This module contains a representation class for EVM instructions and
transitions between them."""
import binascii
import logging

from copy import copy, deepcopy
from typing import cast, Callable, List, Union, Tuple
from datetime import datetime
from math import ceil
from ethereum import utils

from mythril.laser.smt import (
    Extract,
    Expression,
    UDiv,
    simplify,
    Concat,
    ULT,
    UGT,
    BitVec,
    is_true,
    is_false,
    URem,
    SRem,
    If,
    Bool,
    Or,
    Not,
    LShR,
)
from mythril.laser.smt import symbol_factory

import mythril.laser.ethereum.util as helper
from mythril.laser.ethereum import util
from mythril.laser.ethereum.call import get_call_parameters, native_call
from mythril.laser.ethereum.evm_exceptions import (
    VmException,
    StackUnderflowException,
    InvalidJumpDestination,
    InvalidInstruction,
    OutOfGasException,
)
from mythril.laser.ethereum.gas import OPCODE_GAS
from mythril.laser.ethereum.keccak import KeccakFunctionManager
from mythril.laser.ethereum.state.global_state import GlobalState
from mythril.laser.ethereum.transaction import (
    MessageCallTransaction,
    TransactionStartSignal,
    ContractCreationTransaction,
)

from mythril.support.loader import DynLoader

log = logging.getLogger(__name__)

TT256 = 2 ** 256
TT256M1 = 2 ** 256 - 1


class StateTransition(object):
    """Decorator that handles global state copy and original return.

    This decorator calls the decorated instruction mutator function on a
    copy of the state that is passed to it. After the call, the
    resulting new states' program counter is automatically incremented
    if `increment_pc=True`.
    """

    def __init__(self, increment_pc=True, enable_gas=True):
        """

        :param increment_pc:
        :param enable_gas:
        """
        self.increment_pc = increment_pc
        self.enable_gas = enable_gas

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
        min_gas, max_gas = cast(Tuple[int, int], OPCODE_GAS[opcode])
        global_state.mstate.min_gas_used += min_gas
        global_state.mstate.max_gas_used += max_gas
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
            new_global_states = self.call_on_state_copy(func, func_obj, global_state)
            new_global_states = [
                self.accumulate_gas(state) for state in new_global_states
            ]
            return self.increment_states_pc(new_global_states)

        return wrapper


class Instruction:
    """Instruction class is used to mutate a state according to the current
    instruction."""

    def __init__(self, op_code: str, dynamic_loader: DynLoader, iprof=None) -> None:
        """

        :param op_code:
        :param dynamic_loader:
        :param iprof:
        """
        self.dynamic_loader = dynamic_loader
        self.op_code = op_code.upper()
        self.iprof = iprof

    def evaluate(self, global_state: GlobalState, post=False) -> List[GlobalState]:
        """Performs the mutation for this instruction.

        :param global_state:
        :param post:
        :return:
        """
        # Generalize some ops
        log.debug("Evaluating {}".format(self.op_code))
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

        if self.iprof is None:
            result = instruction_mutator(global_state)
        else:
            start_time = datetime.now()
            result = instruction_mutator(global_state)
            end_time = datetime.now()
            self.iprof.record(op, start_time, end_time)

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
        push_value = push_instruction["argument"][2:]

        try:
            length_of_value = 2 * int(push_instruction["opcode"][4:])
        except ValueError:
            raise VmException("Invalid Push instruction")

        push_value += "0" * max(length_of_value - len(push_value), 0)
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
        mstate.stack.append(symbol_factory.BitVecVal(TT256M1, 256) - mstate.stack.pop())
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

        if base.symbolic or exponent.symbolic:

            state.stack.append(
                global_state.new_bitvec(
                    "(" + str(simplify(base)) + ")**(" + str(simplify(exponent)) + ")",
                    256,
                    base.annotations + exponent.annotations,
                )
            )
        else:

            state.stack.append(
                symbol_factory.BitVecVal(
                    pow(base.value, exponent.value, 2 ** 256),
                    256,
                    annotations=base.annotations + exponent.annotations,
                )
            )

        return [global_state]

    @StateTransition()
    def signextend_(self, global_state: GlobalState) -> List[GlobalState]:
        """

        :param global_state:
        :return:
        """
        state = global_state.mstate
        s0, s1 = state.stack.pop(), state.stack.pop()

        try:
            s0 = util.get_concrete_int(s0)
            s1 = util.get_concrete_int(s1)
        except TypeError:
            return []

        if s0 <= 31:
            testbit = s0 * 8 + 7
            if s1 & (1 << testbit):
                state.stack.append(s1 | (TT256 - (1 << testbit)))
            else:
                state.stack.append(s1 & ((1 << testbit) - 1))
        else:
            state.stack.append(s1)

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
        state = global_state.mstate
        environment = global_state.environment
        state.stack.append(environment.calldata.calldatasize)
        return [global_state]

    @StateTransition()
    def calldatacopy_(self, global_state: GlobalState) -> List[GlobalState]:
        """

        :param global_state:
        :return:
        """
        state = global_state.mstate
        environment = global_state.environment
        op0, op1, op2 = state.stack.pop(), state.stack.pop(), state.stack.pop()

        try:
            mstart = util.get_concrete_int(op0)
        except TypeError:
            log.debug("Unsupported symbolic memory offset in CALLDATACOPY")
            return [global_state]

        try:
            dstart = util.get_concrete_int(op1)  # type: Union[int, BitVec]
        except TypeError:
            log.debug("Unsupported symbolic calldata offset in CALLDATACOPY")
            dstart = simplify(op1)

        size_sym = False
        try:
            size = util.get_concrete_int(op2)  # type: Union[int, BitVec]
        except TypeError:
            log.debug("Unsupported symbolic size in CALLDATACOPY")
            size = simplify(op2)
            size_sym = True

        if size_sym:
            state.mem_extend(mstart, 1)
            state.memory[mstart] = global_state.new_bitvec(
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
        size = cast(int, size)
        if size > 0:
            try:
                state.mem_extend(mstart, size)
            except TypeError:
                log.debug(
                    "Memory allocation error: mstart = "
                    + str(mstart)
                    + ", size = "
                    + str(size)
                )
                state.mem_extend(mstart, 1)
                state.memory[mstart] = global_state.new_bitvec(
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
                    state.memory[i + mstart] = new_memory[i]

            except IndexError:
                log.debug("Exception copying calldata to memory")

                state.memory[mstart] = global_state.new_bitvec(
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
        state.stack.append(global_state.new_bitvec("balance_at_" + str(address), 256))
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
    def codesize_(self, global_state: GlobalState) -> List[GlobalState]:
        """

        :param global_state:
        :return:
        """
        state = global_state.mstate
        environment = global_state.environment
        disassembly = environment.code
        state.stack.append(len(disassembly.bytecode) // 2)
        return [global_state]

    @StateTransition(enable_gas=False)
    def sha3_(self, global_state: GlobalState) -> List[GlobalState]:
        """

        :param global_state:
        :return:
        """

        state = global_state.mstate
        op0, op1 = state.stack.pop(), state.stack.pop()

        try:
            index, length = util.get_concrete_int(op0), util.get_concrete_int(op1)
        except TypeError:
            # Can't access symbolic memory offsets
            if isinstance(op0, Expression):
                op0 = simplify(op0)
            state.stack.append(
                symbol_factory.BitVecSym("KECCAC_mem[" + str(op0) + "]", 256)
            )
            gas_tuple = cast(Tuple, OPCODE_GAS["SHA3"])
            state.min_gas_used += gas_tuple[0]
            state.max_gas_used += gas_tuple[1]
            return [global_state]

        min_gas, max_gas = cast(Callable, OPCODE_GAS["SHA3_FUNC"])(length)
        state.min_gas_used += min_gas
        state.max_gas_used += max_gas
        StateTransition.check_gas_usage_limit(global_state)

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
            # length is 0; this only matters for input of the BitVecFuncVal
            data = symbol_factory.BitVecVal(0, 1)

        if data.symbolic:
            argument_str = str(state.memory[index]).replace(" ", "_")
            result = symbol_factory.BitVecFuncSym(
                "KECCAC[{}]".format(argument_str), "keccak256", 256, input_=data
            )
            log.debug("Created BitVecFunc hash.")

        else:
            keccak = utils.sha3(data.value.to_bytes(length, byteorder="big"))
            result = symbol_factory.BitVecFuncVal(
                util.concrete_int_from_bytes(keccak, 0), "keccak256", 256, input_=data
            )
            log.debug("Computed SHA3 Hash: " + str(binascii.hexlify(keccak)))

        state.stack.append(result)
        return [global_state]

    @StateTransition()
    def gasprice_(self, global_state: GlobalState) -> List[GlobalState]:
        """

        :param global_state:
        :return:
        """
        global_state.mstate.stack.append(global_state.new_bitvec("gasprice", 256))
        return [global_state]

    @staticmethod
    def _handle_symbolic_args(
        global_state: GlobalState, concrete_memory_offset: int
    ) -> None:
        """
        In contract creation transaction with dynamic arguments(like arrays, maps) solidity will try to
        execute CODECOPY with code size as len(with_args) - len(without_args) which in our case
        would be 0, hence we are writing 10 symbol words onto the memory on the assumption that
        no one would use 10 array/map arguments for constructor.
        :param global_state: The global state
        :param concrete_memory_offset: The memory offset on which symbols should be written
        """
        no_of_words = ceil(
            min(len(global_state.environment.code.bytecode) / 2, 320) / 32
        )
        global_state.mstate.mem_extend(concrete_memory_offset, 32 * no_of_words)
        for i in range(no_of_words):
            global_state.mstate.memory.write_word_at(
                concrete_memory_offset + i * 32,
                global_state.new_bitvec(
                    "code_{}({})".format(
                        concrete_memory_offset + i * 32,
                        global_state.environment.active_account.contract_name,
                    ),
                    256,
                ),
            )

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

        try:
            concrete_memory_offset = helper.get_concrete_int(memory_offset)
        except TypeError:
            log.debug("Unsupported symbolic memory offset in CODECOPY")
            return [global_state]

        try:
            size = helper.get_concrete_int(size)
            global_state.mstate.mem_extend(concrete_memory_offset, size)

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
            log.debug("Unsupported symbolic code offset in CODECOPY")
            global_state.mstate.mem_extend(concrete_memory_offset, size)
            for i in range(size):
                global_state.mstate.memory[
                    concrete_memory_offset + i
                ] = global_state.new_bitvec(
                    "code({})".format(
                        global_state.environment.active_account.contract_name
                    ),
                    8,
                )
            return [global_state]

        bytecode = global_state.environment.code.bytecode
        if bytecode[0:2] == "0x":
            bytecode = bytecode[2:]

        if size == 0 and isinstance(
            global_state.current_transaction, ContractCreationTransaction
        ):
            if concrete_code_offset >= len(bytecode) // 2:
                self._handle_symbolic_args(global_state, concrete_memory_offset)
                return [global_state]

        for i in range(size):
            if 2 * (concrete_code_offset + i + 1) <= len(bytecode):
                global_state.mstate.memory[concrete_memory_offset + i] = int(
                    bytecode[
                        2
                        * (concrete_code_offset + i) : 2
                        * (concrete_code_offset + i + 1)
                    ],
                    16,
                )
            else:
                global_state.mstate.memory[
                    concrete_memory_offset + i
                ] = global_state.new_bitvec(
                    "code({})".format(
                        global_state.environment.active_account.contract_name
                    ),
                    8,
                )

        return [global_state]

    @StateTransition()
    def extcodesize_(self, global_state: GlobalState) -> List[GlobalState]:
        """

        :param global_state:
        :return:
        """
        state = global_state.mstate
        addr = state.stack.pop()
        environment = global_state.environment
        try:
            addr = hex(helper.get_concrete_int(addr))
        except TypeError:
            log.debug("unsupported symbolic address for EXTCODESIZE")
            state.stack.append(global_state.new_bitvec("extcodesize_" + str(addr), 256))
            return [global_state]

        try:
            code = self.dynamic_loader.dynld(addr)
        except (ValueError, AttributeError) as e:
            log.debug("error accessing contract storage due to: " + str(e))
            state.stack.append(global_state.new_bitvec("extcodesize_" + str(addr), 256))
            return [global_state]

        if code is None:
            state.stack.append(0)
        else:
            state.stack.append(len(code.bytecode) // 2)

        return [global_state]

    @StateTransition
    def extcodehash_(self, global_state: GlobalState) -> List[GlobalState]:
        """

        :param global_state:
        :return: List of global states possible, list of size 1 in this case
        """
        # TODO: To be implemented
        address = global_state.mstate.stack.pop()
        global_state.mstate.stack.append(
            global_state.new_bitvec("extcodehash_{}".format(str(address)), 256)
        )
        return [global_state]

    @StateTransition()
    def extcodecopy_(self, global_state: GlobalState) -> List[GlobalState]:
        """

        :param global_state:
        :return:
        """
        # FIXME: not implemented
        state = global_state.mstate
        addr = state.stack.pop()
        start, s2, size = state.stack.pop(), state.stack.pop(), state.stack.pop()

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
        global_state.mstate.stack.append(global_state.new_bitvec("block_number", 256))
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
        op0 = state.stack.pop()

        log.debug("MLOAD[" + str(op0) + "]")

        try:
            offset = util.get_concrete_int(op0)
        except TypeError:
            log.debug("Can't MLOAD from symbolic index")
            data = global_state.new_bitvec("mem[" + str(simplify(op0)) + "]", 256)
            state.stack.append(data)
            return [global_state]

        state.mem_extend(offset, 32)
        data = state.memory.get_word_at(offset)

        log.debug("Load from memory[" + str(offset) + "]: " + str(data))

        state.stack.append(data)
        return [global_state]

    @StateTransition()
    def mstore_(self, global_state: GlobalState) -> List[GlobalState]:
        """

        :param global_state:
        :return:
        """
        state = global_state.mstate
        op0, value = state.stack.pop(), state.stack.pop()

        try:
            mstart = util.get_concrete_int(op0)
        except TypeError:
            log.debug("MSTORE to symbolic index. Not supported")
            return [global_state]

        try:
            state.mem_extend(mstart, 32)
        except Exception:
            log.debug("Error extending memory, mstart = " + str(mstart) + ", size = 32")

        log.debug("MSTORE to mem[" + str(mstart) + "]: " + str(value))

        state.memory.write_word_at(mstart, value)

        return [global_state]

    @StateTransition()
    def mstore8_(self, global_state: GlobalState) -> List[GlobalState]:
        """

        :param global_state:
        :return:
        """
        state = global_state.mstate
        op0, value = state.stack.pop(), state.stack.pop()

        try:
            offset = util.get_concrete_int(op0)
        except TypeError:
            log.debug("MSTORE to symbolic index. Not supported")
            return [global_state]

        state.mem_extend(offset, 1)

        try:
            value_to_write = (
                util.get_concrete_int(value) % 256
            )  # type: Union[int, BitVec]
        except TypeError:  # BitVec
            value_to_write = Extract(7, 0, value)
        log.debug("MSTORE8 to mem[" + str(offset) + "]: " + str(value_to_write))

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
        log.debug("Storage access at index " + str(index))
        index = simplify(index)

        if not KeccakFunctionManager.is_keccak(index):
            return self._sload_helper(global_state, index)

        storage_keys = global_state.environment.active_account.storage.keys()
        keccak_keys = list(filter(KeccakFunctionManager.is_keccak, storage_keys))

        results = []  # type: List[GlobalState]
        constraints = []

        for keccak_key in keccak_keys:
            key_argument = KeccakFunctionManager.get_argument(keccak_key)
            index_argument = KeccakFunctionManager.get_argument(index)
            if key_argument.size() != index_argument.size():
                continue
            constraints.append((keccak_key, key_argument == index_argument))

        for (keccak_key, constraint) in constraints:
            if constraint in state.constraints:
                results += self._sload_helper(global_state, keccak_key, [constraint])
        if len(results) > 0:
            return results

        for (keccak_key, constraint) in constraints:
            results += self._sload_helper(copy(global_state), keccak_key, [constraint])

        if len(results) > 0:
            return results

        return self._sload_helper(global_state, index)

    @staticmethod
    def _sload_helper(
        global_state: GlobalState, index: Union[str, int], constraints=None
    ):
        """

        :param global_state:
        :param index:
        :param constraints:
        :return:
        """
        try:
            data = global_state.environment.active_account.storage[index]
        except KeyError:
            data = global_state.new_bitvec("storage_" + str(index), 256)
            global_state.environment.active_account.storage[index] = data

        if constraints is not None:
            global_state.mstate.constraints += constraints
            if global_state.mstate.constraints.is_possible is False:
                return []

        global_state.mstate.stack.append(data)
        return [global_state]

    @staticmethod
    def _get_constraints(keccak_keys, this_key, argument):
        """

        :param keccak_keys:
        :param this_key:
        :param argument:
        """
        for keccak_key in keccak_keys:
            if keccak_key == this_key:
                continue
            keccak_argument = KeccakFunctionManager.get_argument(keccak_key)
            yield keccak_argument != argument

    @StateTransition()
    def sstore_(self, global_state: GlobalState) -> List[GlobalState]:
        """

        :param global_state:
        :return:
        """
        state = global_state.mstate
        index, value = state.stack.pop(), state.stack.pop()
        log.debug("Write to storage[" + str(index) + "]")
        index = simplify(index)
        is_keccak = KeccakFunctionManager.is_keccak(index)
        if not is_keccak:
            return self._sstore_helper(global_state, index, value)

        storage_keys = global_state.environment.active_account.storage.keys()

        keccak_keys = filter(KeccakFunctionManager.is_keccak, storage_keys)

        results = []  # type: List[GlobalState]
        new = symbol_factory.Bool(False)

        for keccak_key in keccak_keys:
            key_argument = KeccakFunctionManager.get_argument(
                keccak_key
            )  # type: Expression
            index_argument = KeccakFunctionManager.get_argument(
                index
            )  # type: Expression
            if key_argument.size() != index_argument.size():
                continue

            result = self._sstore_helper(
                copy(global_state), keccak_key, value, key_argument == index_argument
            )
            if len(result) > 0:
                return result

            new = Or(new, cast(Bool, key_argument != index_argument))
        results += self._sstore_helper(copy(global_state), index, value, new)
        if len(results) > 0:
            return results
        # results += self._sstore_helper(copy(global_state), index, value)
        return self._sstore_helper(copy(global_state), index, value)

    @staticmethod
    def _sstore_helper(global_state, index, value, constraint=None):
        """

        :param global_state:
        :param index:
        :param value:
        :param constraint:
        :return:
        """
        try:
            global_state.environment.active_account = deepcopy(
                global_state.environment.active_account
            )
            global_state.accounts[
                global_state.environment.active_account.address
            ] = global_state.environment.active_account

            global_state.environment.active_account.storage[index] = (
                value if not isinstance(value, Expression) else simplify(value)
            )
        except KeyError:
            log.debug("Error writing to storage: Invalid index")

        if constraint is not None:
            global_state.mstate.constraints.append(constraint)
            if global_state.mstate.constraints.is_possible is False:
                return []

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
        min_gas, max_gas = cast(Tuple[int, int], OPCODE_GAS["JUMP"])
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
        min_gas, max_gas = cast(Tuple[int, int], OPCODE_GAS["JUMPI"])
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
            new_state.mstate.constraints.append(negated)
            states.append(new_state)
        else:
            log.debug("Pruned unreachable states.")

        # True case

        # Get jump destination
        index = util.get_instruction_index(disassembly.instruction_list, jump_addr)

        if not index:
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
                new_state.mstate.constraints.append(condi)
                states.append(new_state)
            else:
                log.debug("Pruned unreachable states.")
        return states

    @StateTransition()
    def pc_(self, global_state: GlobalState) -> List[GlobalState]:
        """

        :param global_state:
        :return:
        """
        global_state.mstate.stack.append(global_state.mstate.pc - 1)
        return [global_state]

    @StateTransition()
    def msize_(self, global_state: GlobalState) -> List[GlobalState]:
        """

        :param global_state:
        :return:
        """
        global_state.mstate.stack.append(global_state.new_bitvec("msize", 256))
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

    @StateTransition()
    def log_(self, global_state: GlobalState) -> List[GlobalState]:
        """

        :param global_state:
        :return:
        """
        # TODO: implement me
        state = global_state.mstate
        dpth = int(self.op_code[3:])
        state.stack.pop(), state.stack.pop()
        log_data = [state.stack.pop() for _ in range(dpth)]
        # Not supported
        return [global_state]

    @StateTransition()
    def create_(self, global_state: GlobalState) -> List[GlobalState]:
        """

        :param global_state:
        :return:
        """
        # TODO: implement me
        state = global_state.mstate
        state.stack.pop(), state.stack.pop(), state.stack.pop()
        # Not supported
        state.stack.append(0)
        return [global_state]

    @StateTransition()
    def create2_(self, global_state: GlobalState) -> List[GlobalState]:
        """

        :param global_state:
        :return:
        """
        # TODO: implement me
        state = global_state.mstate
        endowment, memory_start, memory_length, salt = (
            state.stack.pop(),
            state.stack.pop(),
            state.stack.pop(),
            state.stack.pop(),
        )
        # Not supported
        state.stack.append(0)
        return [global_state]

    @StateTransition()
    def return_(self, global_state: GlobalState):
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
        global_state.current_transaction.end(global_state, return_data)

    @StateTransition()
    def suicide_(self, global_state: GlobalState):
        """

        :param global_state:
        """
        target = global_state.mstate.stack.pop()
        account_created = False
        # Often the target of the suicide instruction will be symbolic
        # If it isn't then well transfer the balance to the indicated contract
        if isinstance(target, BitVec) and not target.symbolic:
            target = "0x" + hex(target.value)[-40:]
        if isinstance(target, str):
            try:
                global_state.world_state[
                    target
                ].balance += global_state.environment.active_account.balance
            except KeyError:
                global_state.world_state.create_account(
                    address=target,
                    balance=global_state.environment.active_account.balance,
                )
                account_created = True

        global_state.environment.active_account = deepcopy(
            global_state.environment.active_account
        )
        global_state.accounts[
            global_state.environment.active_account.address
        ] = global_state.environment.active_account

        global_state.environment.active_account.balance = 0
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

    @StateTransition()
    def call_(self, global_state: GlobalState) -> List[GlobalState]:
        """

        :param global_state:
        :return:
        """
        instr = global_state.get_current_instruction()
        environment = global_state.environment

        try:
            callee_address, callee_account, call_data, value, gas, memory_out_offset, memory_out_size = get_call_parameters(
                global_state, self.dynamic_loader, True
            )
        except ValueError as e:
            log.debug(
                "Could not determine required parameters for call, putting fresh symbol on the stack. \n{}".format(
                    e
                )
            )
            # TODO: decide what to do in this case
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
            caller=symbol_factory.BitVecVal(
                int(environment.active_account.address, 16), 256
            ),
            callee_account=callee_account,
            call_data=call_data,
            call_value=value,
        )
        raise TransactionStartSignal(transaction, self.op_code)

    @StateTransition()
    def call_post(self, global_state: GlobalState) -> List[GlobalState]:
        """

        :param global_state:
        :return:
        """
        instr = global_state.get_current_instruction()

        try:
            callee_address, callee_account, call_data, value, gas, memory_out_offset, memory_out_size = get_call_parameters(
                global_state, self.dynamic_loader, True
            )
        except ValueError as e:
            log.debug(
                "Could not determine required parameters for call, putting fresh symbol on the stack. \n{}".format(
                    e
                )
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
            global_state.mstate.constraints.append(return_value == 0)

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
        global_state.mstate.constraints.append(return_value == 1)

        return [global_state]

    @StateTransition()
    def callcode_(self, global_state: GlobalState) -> List[GlobalState]:
        """

        :param global_state:
        :return:
        """
        instr = global_state.get_current_instruction()
        environment = global_state.environment

        try:
            callee_address, callee_account, call_data, value, gas, _, _ = get_call_parameters(
                global_state, self.dynamic_loader, True
            )
        except ValueError as e:
            log.debug(
                "Could not determine required parameters for call, putting fresh symbol on the stack. \n{}".format(
                    e
                )
            )
            global_state.mstate.stack.append(
                global_state.new_bitvec("retval_" + str(instr["address"]), 256)
            )
            return [global_state]

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
        )
        raise TransactionStartSignal(transaction, self.op_code)

    @StateTransition()
    def callcode_post(self, global_state: GlobalState) -> List[GlobalState]:
        """

        :param global_state:
        :return:
        """
        instr = global_state.get_current_instruction()

        try:
            callee_address, _, _, value, _, memory_out_offset, memory_out_size = get_call_parameters(
                global_state, self.dynamic_loader, True
            )
        except ValueError as e:
            log.debug(
                "Could not determine required parameters for call, putting fresh symbol on the stack. \n{}".format(
                    e
                )
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
            global_state.mstate.constraints.append(return_value == 0)
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
        global_state.mstate.constraints.append(return_value == 1)
        return [global_state]

    @StateTransition()
    def delegatecall_(self, global_state: GlobalState) -> List[GlobalState]:
        """

        :param global_state:
        :return:
        """
        instr = global_state.get_current_instruction()
        environment = global_state.environment

        try:
            callee_address, callee_account, call_data, value, gas, _, _ = get_call_parameters(
                global_state, self.dynamic_loader
            )
        except ValueError as e:
            log.debug(
                "Could not determine required parameters for call, putting fresh symbol on the stack. \n{}".format(
                    e
                )
            )
            global_state.mstate.stack.append(
                global_state.new_bitvec("retval_" + str(instr["address"]), 256)
            )
            return [global_state]

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
        )
        raise TransactionStartSignal(transaction, self.op_code)

    @StateTransition()
    def delegatecall_post(self, global_state: GlobalState) -> List[GlobalState]:
        """

        :param global_state:
        :return:
        """
        instr = global_state.get_current_instruction()

        try:
            callee_address, _, _, value, _, memory_out_offset, memory_out_size = get_call_parameters(
                global_state, self.dynamic_loader
            )
        except ValueError as e:
            log.debug(
                "Could not determine required parameters for call, putting fresh symbol on the stack. \n{}".format(
                    e
                )
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
            global_state.mstate.constraints.append(return_value == 0)
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
        global_state.mstate.constraints.append(return_value == 1)
        return [global_state]

    @StateTransition()
    def staticcall_(self, global_state: GlobalState) -> List[GlobalState]:
        """

        :param global_state:
        :return:
        """
        # TODO: implement me
        instr = global_state.get_current_instruction()
        try:
            callee_address, callee_account, call_data, value, gas, memory_out_offset, memory_out_size = get_call_parameters(
                global_state, self.dynamic_loader
            )
        except ValueError as e:
            log.debug(
                "Could not determine required parameters for call, putting fresh symbol on the stack. \n{}".format(
                    e
                )
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

        global_state.mstate.stack.append(
            global_state.new_bitvec("retval_" + str(instr["address"]), 256)
        )
        return [global_state]
