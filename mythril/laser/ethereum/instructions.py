import binascii
import logging
from copy import copy, deepcopy

from ethereum import utils
from z3 import Extract, UDiv, simplify, Concat, ULT, UGT, BitVecNumRef, Not, \
    is_false, is_expr, ExprRef, URem, SRem, BitVec, Solver, is_true, BitVecVal, If, BoolRef, Or

import mythril.laser.ethereum.natives as natives
import mythril.laser.ethereum.util as helper
from mythril.laser.ethereum import util
from mythril.laser.ethereum.call import get_call_parameters
from mythril.laser.ethereum.evm_exceptions import VmException, StackUnderflowException, InvalidJumpDestination
from mythril.laser.ethereum.keccak import KeccakFunctionManager
from mythril.laser.ethereum.state import GlobalState, CalldataType
from mythril.laser.ethereum.transaction import MessageCallTransaction, TransactionStartSignal, \
    ContractCreationTransaction

TT256 = 2 ** 256
TT256M1 = 2 ** 256 - 1

keccak_function_manager = KeccakFunctionManager()


class StateTransition(object):
    """Decorator that handles global state copy and original return.

    This decorator calls the decorated instruction mutator function on a copy of the state that
    is passed to it. After the call, the resulting new states' program counter is automatically
    incremented if `increment_pc=True`.
    """

    def __init__(self, increment_pc=True):
        self.increment_pc = increment_pc

    @staticmethod
    def call_on_state_copy(func, func_obj, state):
        global_state_copy = copy(state)
        return func(func_obj, global_state_copy)

    def increment_states_pc(self, states):
        if self.increment_pc:
            for state in states:
                state.mstate.pc += 1
        return states

    def __call__(self, func):
        def wrapper(func_obj, global_state):
            new_global_states = self.call_on_state_copy(
                func,
                func_obj,
                global_state
            )
            return self.increment_states_pc(new_global_states)
        return wrapper


class Instruction:
    """
    Instruction class is used to mutate a state according to the current instruction
    """

    def __init__(self, op_code, dynamic_loader):
        self.dynamic_loader = dynamic_loader
        self.op_code = op_code

    def evaluate(self, global_state, post=False):
        """ Performs the mutation for this instruction """
        # Generalize some ops
        logging.debug("Evaluating {}".format(self.op_code))
        op = self.op_code.lower()
        if self.op_code.startswith("PUSH"):
            op = "push"
        elif self.op_code.startswith("DUP"):
            op = "dup"
        elif self.op_code.startswith("SWAP"):
            op = "swap"
        elif self.op_code.startswith("LOG"):
            op = "log"

        instruction_mutator = getattr(self, op + '_', None) if not post else getattr(self, op + '_' + 'post', None)

        if instruction_mutator is None:
            raise NotImplementedError

        return instruction_mutator(global_state)

    @StateTransition()
    def jumpdest_(self, global_state):
        return [global_state]

    @StateTransition()
    def push_(self, global_state):
        push_instruction = global_state.get_current_instruction()
        push_value = push_instruction['argument'][2:]

        try:
            length_of_value = 2*int(push_instruction['opcode'][4:])
        except ValueError:
            raise VmException('Invalid Push instruction')

        push_value += "0" * max(length_of_value - len(push_value), 0)
        global_state.mstate.stack.append(BitVecVal(int(push_value, 16), 256))
        return [global_state]

    @StateTransition()
    def dup_(self, global_state):
        value = int(global_state.get_current_instruction()['opcode'][3:], 10)
        global_state.mstate.stack.append(global_state.mstate.stack[-value])
        return [global_state]

    @StateTransition()
    def swap_(self, global_state):
        depth = int(self.op_code[4:])
        stack = global_state.mstate.stack
        stack[-depth - 1], stack[-1] = stack[-1], stack[-depth - 1]
        return [global_state]

    @StateTransition()
    def pop_(self, global_state):
        global_state.mstate.stack.pop()
        return [global_state]

    @StateTransition()
    def and_(self, global_state):
        stack = global_state.mstate.stack
        op1, op2 = stack.pop(), stack.pop()
        if type(op1) == BoolRef:
            op1 = If(op1, BitVecVal(1, 256), BitVecVal(0, 256))
        if type(op2) == BoolRef:
            op2 = If(op2, BitVecVal(1, 256), BitVecVal(0, 256))

        stack.append(op1 & op2)

        return [global_state]

    @StateTransition()
    def or_(self, global_state):
        stack = global_state.mstate.stack
        op1, op2 = stack.pop(), stack.pop()

        if type(op1) == BoolRef:
            op1 = If(op1, BitVecVal(1, 256), BitVecVal(0, 256))

        if type(op2) == BoolRef:
            op2 = If(op2, BitVecVal(1, 256), BitVecVal(0, 256))

        stack.append(op1 | op2)

        return [global_state]

    @StateTransition()
    def xor_(self, global_state):
        mstate = global_state.mstate
        mstate.stack.append(mstate.stack.pop() ^ mstate.stack.pop())
        return [global_state]

    @StateTransition()
    def not_(self, global_state: GlobalState):
        mstate = global_state.mstate
        mstate.stack.append(TT256M1 - mstate.stack.pop())
        return [global_state]

    @StateTransition()
    def byte_(self, global_state):
        mstate = global_state.mstate
        op0, op1 = mstate.stack.pop(), mstate.stack.pop()
        if not isinstance(op1, ExprRef):
            op1 = BitVecVal(op1, 256)
        try:
            index = util.get_concrete_int(op0)
            offset = (31 - index) * 8
            if offset >= 0:
                result = simplify(Concat(BitVecVal(0, 248), Extract(offset + 7, offset, op1)))
            else:
                result = 0
        except AttributeError:
            logging.debug("BYTE: Unsupported symbolic byte offset")
            result = global_state.new_bitvec(str(simplify(op1)) + "[" + str(simplify(op0)) + "]", 256)

        mstate.stack.append(result)
        return [global_state]

    # Arithmetic
    @StateTransition()
    def add_(self, global_state):
        global_state.mstate.stack.append(
            (helper.pop_bitvec(global_state.mstate) + helper.pop_bitvec(global_state.mstate)))
        return [global_state]

    @StateTransition()
    def sub_(self, global_state):
        global_state.mstate.stack.append(
            (helper.pop_bitvec(global_state.mstate) - helper.pop_bitvec(global_state.mstate)))
        return [global_state]

    @StateTransition()
    def mul_(self, global_state):
        global_state.mstate.stack.append(
            (helper.pop_bitvec(global_state.mstate) * helper.pop_bitvec(global_state.mstate)))
        return [global_state]

    @StateTransition()
    def div_(self, global_state):
        op0, op1 = util.pop_bitvec(global_state.mstate), util.pop_bitvec(global_state.mstate)
        if op1 == 0:
            global_state.mstate.stack.append(BitVecVal(0, 256))
        else:
            global_state.mstate.stack.append(UDiv(op0, op1))
        return [global_state]

    @StateTransition()
    def sdiv_(self, global_state):
        s0, s1 = util.pop_bitvec(global_state.mstate), util.pop_bitvec(global_state.mstate)
        if s1 == 0:
            global_state.mstate.stack.append(BitVecVal(0, 256))
        else:
            global_state.mstate.stack.append(s0 / s1)
        return [global_state]

    @StateTransition()
    def mod_(self, global_state):
        s0, s1 = util.pop_bitvec(global_state.mstate), util.pop_bitvec(global_state.mstate)
        global_state.mstate.stack.append(0 if s1 == 0 else URem(s0, s1))
        return [global_state]

    @StateTransition()
    def smod_(self, global_state):
        s0, s1 = util.pop_bitvec(global_state.mstate), util.pop_bitvec(global_state.mstate)
        global_state.mstate.stack.append(0 if s1 == 0 else SRem(s0, s1))
        return [global_state]

    @StateTransition()
    def addmod_(self, global_state):
        s0, s1, s2 = util.pop_bitvec(global_state.mstate), util.pop_bitvec(global_state.mstate), util.pop_bitvec(
            global_state.mstate)
        global_state.mstate.stack.append(URem(URem(s0, s2) + URem(s1, s2), s2))
        return [global_state]

    @StateTransition()
    def mulmod_(self, global_state):
        s0, s1, s2 = util.pop_bitvec(global_state.mstate), util.pop_bitvec(global_state.mstate), util.pop_bitvec(
            global_state.mstate)
        global_state.mstate.stack.append(URem(URem(s0, s2) * URem(s1, s2), s2))
        return [global_state]

    @StateTransition()
    def exp_(self, global_state):
        state = global_state.mstate

        base, exponent = util.pop_bitvec(state), util.pop_bitvec(state)
        if (type(base) != BitVecNumRef) or (type(exponent) != BitVecNumRef):
            state.stack.append(global_state.new_bitvec("(" + str(simplify(base)) + ")**(" + str(simplify(exponent)) + ")", 256))
        else:
            state.stack.append(pow(base.as_long(), exponent.as_long(), 2**256))

        return [global_state]

    @StateTransition()
    def signextend_(self, global_state):
        state = global_state.mstate
        s0, s1 = state.stack.pop(), state.stack.pop()

        try:
            s0 = util.get_concrete_int(s0)
            s1 = util.get_concrete_int(s1)

            if s0 <= 31:
                testbit = s0 * 8 + 7
                if s1 & (1 << testbit):
                    state.stack.append(s1 | (TT256 - (1 << testbit)))
                else:
                    state.stack.append(s1 & ((1 << testbit) - 1))
            else:
                state.stack.append(s1)
            # TODO: broad exception handler
        except:
            return []

        return [global_state]

    # Comparisons
    @StateTransition()
    def lt_(self, global_state):
        state = global_state.mstate
        exp = ULT(util.pop_bitvec(state), util.pop_bitvec(state))
        state.stack.append(exp)
        return [global_state]

    @StateTransition()
    def gt_(self, global_state):
        state = global_state.mstate
        exp = UGT(util.pop_bitvec(state), util.pop_bitvec(state))
        state.stack.append(exp)
        return [global_state]

    @StateTransition()
    def slt_(self, global_state):
        state = global_state.mstate
        exp = util.pop_bitvec(state) < util.pop_bitvec(state)
        state.stack.append(exp)
        return [global_state]

    @StateTransition()
    def sgt_(self, global_state):
        state = global_state.mstate

        exp = util.pop_bitvec(state) > util.pop_bitvec(state)
        state.stack.append(exp)
        return [global_state]

    @StateTransition()
    def eq_(self, global_state):
        state = global_state.mstate

        op1 = state.stack.pop()
        op2 = state.stack.pop()

        if type(op1) == BoolRef:
            op1 = If(op1, BitVecVal(1, 256), BitVecVal(0, 256))

        if type(op2) == BoolRef:
            op2 = If(op2, BitVecVal(1, 256), BitVecVal(0, 256))

        exp = op1 == op2

        state.stack.append(exp)
        return [global_state]

    @StateTransition()
    def iszero_(self, global_state):
        state = global_state.mstate

        val = state.stack.pop()
        exp = val == False if type(val) == BoolRef else val == 0
        state.stack.append(exp)

        return [global_state]

    # Call data
    @StateTransition()
    def callvalue_(self, global_state):
        state = global_state.mstate
        environment = global_state.environment
        state.stack.append(environment.callvalue)

        return [global_state]

    @StateTransition()
    def calldataload_(self, global_state):
        state = global_state.mstate
        environment = global_state.environment
        op0 = state.stack.pop()

        try:
            offset = util.get_concrete_int(simplify(op0))
            b = environment.calldata[offset]
        except AttributeError:
            logging.debug("CALLDATALOAD: Unsupported symbolic index")
            state.stack.append(global_state.new_bitvec(
                "calldata_" + str(environment.active_account.contract_name) + "[" + str(simplify(op0)) + "]", 256))
            return [global_state]
        except IndexError:
            logging.debug("Calldata not set, using symbolic variable instead")
            state.stack.append(global_state.new_bitvec(
                "calldata_" + str(environment.active_account.contract_name) + "[" + str(simplify(op0)) + "]", 256))
            return [global_state]

        if type(b) == int:
            val = b''

            try:
                for i in range(offset, offset + 32):
                    val += environment.calldata[i].to_bytes(1, byteorder='big')

                logging.debug("Final value: " + str(int.from_bytes(val, byteorder='big')))
                state.stack.append(BitVecVal(int.from_bytes(val, byteorder='big'), 256))
            # FIXME: broad exception catch
            except:
                state.stack.append(global_state.new_bitvec(
                    "calldata_" + str(environment.active_account.contract_name) + "[" + str(simplify(op0)) + "]", 256))
        else:
            # symbolic variable
            state.stack.append(global_state.new_bitvec(
                "calldata_" + str(environment.active_account.contract_name) + "[" + str(simplify(op0)) + "]", 256))

        return [global_state]

    @StateTransition()
    def calldatasize_(self, global_state):
        state = global_state.mstate
        environment = global_state.environment
        if environment.calldata_type == CalldataType.SYMBOLIC:
            state.stack.append(global_state.new_bitvec("calldatasize_" + environment.active_account.contract_name, 256))
        else:
            state.stack.append(BitVecVal(len(environment.calldata), 256))
        return [global_state]

    @StateTransition()
    def calldatacopy_(self, global_state):
        state = global_state.mstate
        environment = global_state.environment
        op0, op1, op2 = state.stack.pop(), state.stack.pop(), state.stack.pop()

        try:
            mstart = util.get_concrete_int(op0)
            # FIXME: broad exception catch
        except:
            logging.debug("Unsupported symbolic memory offset in CALLDATACOPY")
            return [global_state]

        dstart_sym = False
        try:
            dstart = util.get_concrete_int(op1)
            # FIXME: broad exception catch
        except:
            logging.debug("Unsupported symbolic calldata offset in CALLDATACOPY")
            dstart = simplify(op1)
            dstart_sym = True

        size_sym = False
        try:
            size = util.get_concrete_int(op2)
            # FIXME: broad exception catch
        except:
            logging.debug("Unsupported symbolic size in CALLDATACOPY")
            size = simplify(op2)
            size_sym = True

        if dstart_sym or size_sym:
            state.mem_extend(mstart, 1)
            state.memory[mstart] = global_state.new_bitvec(
                "calldata_" + str(environment.active_account.contract_name) + "[" + str(dstart) + ": + " + str(
                    size) + "]", 256)
            return [global_state]

        if size > 0:
            try:
                state.mem_extend(mstart, size)
            # FIXME: broad exception catch
            except:
                logging.debug("Memory allocation error: mstart = " + str(mstart) + ", size = " + str(size))
                state.mem_extend(mstart, 1)
                state.memory[mstart] = global_state.new_bitvec(
                    "calldata_" + str(environment.active_account.contract_name) + "[" + str(dstart) + ": + " + str(
                        size) + "]", 256)
                return [global_state]

            try:
                i_data = environment.calldata[dstart]

                for i in range(mstart, mstart + size):
                    state.memory[i] = environment.calldata[i_data]
                    i_data += 1
            except:
                logging.debug("Exception copying calldata to memory")

                state.memory[mstart] = global_state.new_bitvec(
                    "calldata_" + str(environment.active_account.contract_name) + "[" + str(dstart) + ": + " + str(
                        size) + "]", 256)
        return [global_state]

    # Environment
    @StateTransition()
    def address_(self, global_state):
        state = global_state.mstate
        environment = global_state.environment
        state.stack.append(environment.address)
        return [global_state]

    @StateTransition()
    def balance_(self, global_state):
        state = global_state.mstate
        address = state.stack.pop()
        state.stack.append(global_state.new_bitvec("balance_at_" + str(address), 256))
        return [global_state]

    @StateTransition()
    def origin_(self, global_state):
        state = global_state.mstate
        environment = global_state.environment
        state.stack.append(environment.origin)
        return [global_state]

    @StateTransition()
    def caller_(self, global_state):
        state = global_state.mstate
        environment = global_state.environment
        state.stack.append(environment.sender)
        return [global_state]

    @StateTransition()
    def codesize_(self, global_state):
        state = global_state.mstate
        environment = global_state.environment
        disassembly = environment.code
        state.stack.append(len(disassembly.bytecode) // 2)
        return [global_state]

    @StateTransition()
    def sha3_(self, global_state):
        global keccak_function_manager

        state = global_state.mstate
        environment = global_state.environment
        op0, op1 = state.stack.pop(), state.stack.pop()

        try:
            index, length = util.get_concrete_int(op0), util.get_concrete_int(op1)
        # FIXME: broad exception catch
        except:
            # Can't access symbolic memory offsets
            if is_expr(op0):
                op0 = simplify(op0)
            state.stack.append(BitVec("KECCAC_mem[" + str(op0) + "]", 256))
            return [global_state]

        try:
            state.mem_extend(index, length)
            data = b''.join([util.get_concrete_int(i).to_bytes(1, byteorder='big')
                             for i in state.memory[index: index + length]])

        except AttributeError:
            argument = str(state.memory[index]).replace(" ", "_")

            result = BitVec("KECCAC[{}]".format(argument), 256)
            keccak_function_manager.add_keccak(result, state.memory[index])
            state.stack.append(result)
            return [global_state]

        keccak = utils.sha3(utils.bytearray_to_bytestr(data))
        logging.debug("Computed SHA3 Hash: " + str(binascii.hexlify(keccak)))

        state.stack.append(BitVecVal(util.concrete_int_from_bytes(keccak, 0), 256))
        return [global_state]

    @StateTransition()
    def gasprice_(self, global_state):
        global_state.mstate.stack.append(global_state.new_bitvec("gasprice", 256))
        return [global_state]

    @StateTransition()
    def codecopy_(self, global_state):
        memory_offset, code_offset, size = global_state.mstate.stack.pop(), global_state.mstate.stack.pop(), global_state.mstate.stack.pop()

        try:
            concrete_memory_offset = helper.get_concrete_int(memory_offset)
        except AttributeError:
            logging.debug("Unsupported symbolic memory offset in CODECOPY")
            return [global_state]

        try:
            concrete_size = helper.get_concrete_int(size)
            global_state.mstate.mem_extend(concrete_memory_offset, concrete_size)
        except:
            # except both attribute error and Exception
            global_state.mstate.mem_extend(concrete_memory_offset, 1)
            global_state.mstate.memory[concrete_memory_offset] = \
                global_state.new_bitvec("code({})".format(global_state.environment.active_account.contract_name), 256)
            return [global_state]

        try:
            concrete_code_offset = helper.get_concrete_int(code_offset)
        except AttributeError:
            logging.debug("Unsupported symbolic code offset in CODECOPY")
            global_state.mstate.mem_extend(concrete_memory_offset, concrete_size)
            for i in range(concrete_size):
                global_state.mstate.memory[concrete_memory_offset + i] = \
                    global_state.new_bitvec("code({})".format(global_state.environment.active_account.contract_name), 256)
            return [global_state]

        bytecode = global_state.environment.code.bytecode

        if concrete_size == 0 and isinstance(global_state.current_transaction, ContractCreationTransaction):
            if concrete_code_offset >= len(global_state.environment.code.bytecode) // 2:
                global_state.mstate.mem_extend(concrete_memory_offset, 1)
                global_state.mstate.memory[concrete_memory_offset] = \
                    global_state.new_bitvec("code({})".format(global_state.environment.active_account.contract_name), 256)
                return [global_state]

        for i in range(concrete_size):
            if 2 * (concrete_code_offset + i + 1) <= len(bytecode):
                global_state.mstate.memory[concrete_memory_offset + i] =\
                    int(bytecode[2*(concrete_code_offset + i): 2*(concrete_code_offset + i + 1)], 16)
            else:
                global_state.mstate.memory[concrete_memory_offset + i] = \
                    global_state.new_bitvec("code({})".format(global_state.environment.active_account.contract_name), 256)

        return [global_state]

    @StateTransition()
    def extcodesize_(self, global_state):
        state = global_state.mstate
        addr = state.stack.pop()
        environment = global_state.environment
        try:
            addr = hex(helper.get_concrete_int(addr))
        except AttributeError:
            logging.info("unsupported symbolic address for EXTCODESIZE")
            state.stack.append(global_state.new_bitvec("extcodesize_" + str(addr), 256))
            return [global_state]

        try:
            code = self.dynamic_loader.dynld(environment.active_account.address, addr)
        except Exception as e:
            logging.info("error accessing contract storage due to: " + str(e))
            state.stack.append(global_state.new_bitvec("extcodesize_" + str(addr), 256))
            return [global_state]

        if code is None:
            state.stack.append(0)
        else:
            state.stack.append(len(code.bytecode) // 2)

        return [global_state]

    @StateTransition()
    def extcodecopy_(self, global_state):
        # FIXME: not implemented
        state = global_state.mstate
        addr = state.stack.pop()
        start, s2, size = state.stack.pop(), state.stack.pop(), state.stack.pop()
        return [global_state]

    @StateTransition()
    def returndatasize_(self, global_state):
        global_state.mstate.stack.append(global_state.new_bitvec("returndatasize", 256))
        return [global_state]

    @StateTransition()
    def blockhash_(self, global_state):
        state = global_state.mstate
        blocknumber = state.stack.pop()
        state.stack.append(global_state.new_bitvec("blockhash_block_" + str(blocknumber), 256))
        return [global_state]

    @StateTransition()
    def coinbase_(self, global_state):
        global_state.mstate.stack.append(global_state.new_bitvec("coinbase", 256))
        return [global_state]

    @StateTransition()
    def timestamp_(self, global_state):
        global_state.mstate.stack.append(global_state.new_bitvec("timestamp", 256))
        return [global_state]

    @StateTransition()
    def number_(self, global_state):
        global_state.mstate.stack.append(global_state.new_bitvec("block_number", 256))
        return [global_state]

    @StateTransition()
    def difficulty_(self, global_state):
        global_state.mstate.stack.append(global_state.new_bitvec("block_difficulty", 256))
        return [global_state]

    @StateTransition()
    def gaslimit_(self, global_state):
        global_state.mstate.stack.append(global_state.new_bitvec("block_gaslimit", 256))
        return [global_state]

    # Memory operations
    @StateTransition()
    def mload_(self, global_state):
        state = global_state.mstate
        op0 = state.stack.pop()

        logging.debug("MLOAD[" + str(op0) + "]")

        try:
            offset = util.get_concrete_int(op0)
        except AttributeError:
            logging.debug("Can't MLOAD from symbolic index")
            data = global_state.new_bitvec("mem[" + str(simplify(op0)) + "]", 256)
            state.stack.append(data)
            return [global_state]

        try:
            data = util.concrete_int_from_bytes(state.memory, offset)
        except IndexError:  # Memory slot not allocated
            data = global_state.new_bitvec("mem[" + str(offset) + "]", 256)
        except TypeError:  # Symbolic memory
            data = state.memory[offset]

        logging.debug("Load from memory[" + str(offset) + "]: " + str(data))

        state.stack.append(data)
        return [global_state]

    @StateTransition()
    def mstore_(self, global_state):
        state = global_state.mstate
        op0, value = state.stack.pop(), state.stack.pop()

        try:
            mstart = util.get_concrete_int(op0)
        except AttributeError:
            logging.debug("MSTORE to symbolic index. Not supported")
            return [global_state]

        try:
            state.mem_extend(mstart, 32)
        except Exception:
            logging.debug("Error extending memory, mstart = " + str(mstart) + ", size = 32")

        logging.debug("MSTORE to mem[" + str(mstart) + "]: " + str(value))

        try:
            # Attempt to concretize value
            _bytes = util.concrete_int_to_bytes(value)

            i = 0

            for b in _bytes:
                state.memory[mstart + i] = _bytes[i]
                i += 1
        except:
            try:
                state.memory[mstart] = value
            except:
                logging.debug("Invalid memory access")

        return [global_state]

    @StateTransition()
    def mstore8_(self, global_state):
        state = global_state.mstate
        op0, value = state.stack.pop(), state.stack.pop()

        try:
            offset = util.get_concrete_int(op0)
        except AttributeError:
            logging.debug("MSTORE to symbolic index. Not supported")
            return [global_state]

        state.mem_extend(offset, 1)

        state.memory[offset] = value % 256
        return [global_state]

    @StateTransition()
    def sload_(self, global_state):
        global keccak_function_manager
        
        state = global_state.mstate
        index = state.stack.pop()
        logging.debug("Storage access at index " + str(index))

        try:
            index = util.get_concrete_int(index)
            return self._sload_helper(global_state, index)

        except AttributeError:
            if not keccak_function_manager.is_keccak(index):
                return self._sload_helper(global_state, str(index))

            storage_keys = global_state.environment.active_account.storage.keys()
            keccak_keys = list(filter(keccak_function_manager.is_keccak, storage_keys))

            results = []
            constraints = []

            for keccak_key in keccak_keys:
                key_argument = keccak_function_manager.get_argument(keccak_key)
                index_argument = keccak_function_manager.get_argument(index)
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
            
            return self._sload_helper(global_state, str(index))

    def _sload_helper(self, global_state, index, constraints=None):
        try:
            data = global_state.environment.active_account.storage[index]
        except KeyError:
            data = global_state.new_bitvec("storage_" + str(index), 256)
            global_state.environment.active_account.storage[index] = data

        if constraints is not None:
            global_state.mstate.constraints += constraints

        global_state.mstate.stack.append(data)
        return [global_state]


    def _get_constraints(self, keccak_keys, this_key, argument):
        global keccak_function_manager
        for keccak_key in keccak_keys:
            if keccak_key == this_key:
                continue
            keccak_argument = keccak_function_manager.get_argument(keccak_key)
            yield keccak_argument != argument

    @StateTransition()
    def sstore_(self, global_state):
        global keccak_function_manager
        state = global_state.mstate
        index, value = state.stack.pop(), state.stack.pop()

        logging.debug("Write to storage[" + str(index) + "]")

        try:
            index = util.get_concrete_int(index)
            return self._sstore_helper(global_state, index, value)
        except AttributeError:
            is_keccak = keccak_function_manager.is_keccak(index)
            if not is_keccak:
                return self._sstore_helper(global_state, str(index), value)

            storage_keys = global_state.environment.active_account.storage.keys()
            keccak_keys = filter(keccak_function_manager.is_keccak, storage_keys)

            solver = Solver()
            solver.set(timeout=1000)

            results = []
            new = False

            for keccak_key in keccak_keys:
                key_argument = keccak_function_manager.get_argument(keccak_key)
                index_argument = keccak_function_manager.get_argument(index)

                if is_true(key_argument == index_argument):
                    return self._sstore_helper(copy(global_state), keccak_key, value, key_argument == index_argument)

                results += self._sstore_helper(copy(global_state), keccak_key, value, key_argument == index_argument)

                new = Or(new, key_argument != index_argument)

            if len(results) > 0:
                results += self._sstore_helper(copy(global_state), str(index), value, new)
                return results

            return self._sstore_helper(global_state, str(index), value)

    def _sstore_helper(self, global_state, index, value, constraint=None):
        try:
            global_state.environment.active_account = deepcopy(global_state.environment.active_account)
            global_state.accounts[
                global_state.environment.active_account.address] = global_state.environment.active_account

            global_state.environment.active_account.storage[index] =\
                value if not isinstance(value, ExprRef) else simplify(value)
        except KeyError:
            logging.debug("Error writing to storage: Invalid index")

        if constraint is not None:
            global_state.mstate.constraints.append(constraint)

        return [global_state]

    @StateTransition(increment_pc=False)
    def jump_(self, global_state):
        state = global_state.mstate
        disassembly = global_state.environment.code
        try:
            jump_addr = util.get_concrete_int(state.stack.pop())
        except AttributeError:
            raise InvalidJumpDestination("Invalid jump argument (symbolic address)")
        except IndexError:
            raise StackUnderflowException()

        index = util.get_instruction_index(disassembly.instruction_list, jump_addr)
        if index is None:
            raise InvalidJumpDestination("JUMP to invalid address")

        op_code = disassembly.instruction_list[index]['opcode']

        if op_code != "JUMPDEST":
            raise InvalidJumpDestination("Skipping JUMP to invalid destination (not JUMPDEST): " + str(jump_addr))

        new_state = copy(global_state)
        new_state.mstate.pc = index
        new_state.mstate.depth += 1

        return [new_state]

    @StateTransition(increment_pc=False)
    def jumpi_(self, global_state):
        state = global_state.mstate
        disassembly = global_state.environment.code
        states = []

        op0, condition = state.stack.pop(), state.stack.pop()

        try:
            jump_addr = util.get_concrete_int(op0)
            # FIXME: to broad exception handler
        except:
            logging.debug("Skipping JUMPI to invalid destination.")
            global_state.mstate.pc += 1
            return [global_state]

        # False case
        negated = simplify(Not(condition)) if type(condition) == BoolRef else condition == 0

        if (type(negated) == bool and negated) or (type(negated) == BoolRef and not is_false(negated)):
            new_state = copy(global_state)
            new_state.mstate.depth += 1
            new_state.mstate.pc += 1
            new_state.mstate.constraints.append(negated)
            states.append(new_state)
        else:
            logging.debug("Pruned unreachable states.")

        # True case

        # Get jump destination
        index = util.get_instruction_index(disassembly.instruction_list, jump_addr)
        if not index:
            logging.debug("Invalid jump destination: " + str(jump_addr))
            return states

        instr = disassembly.instruction_list[index]

        condi = simplify(condition) if type(condition) == BoolRef else condition != 0
        if instr['opcode'] == "JUMPDEST":
            if (type(condi) == bool and condi) or (type(condi) == BoolRef and not is_false(condi)):
                new_state = copy(global_state)
                new_state.mstate.pc = index
                new_state.mstate.depth += 1
                new_state.mstate.constraints.append(condi)
                states.append(new_state)
            else:
                logging.debug("Pruned unreachable states.")
        return states

    @StateTransition()
    def pc_(self, global_state):
        global_state.mstate.stack.append(global_state.mstate.pc - 1)
        return [global_state]

    @StateTransition()
    def msize_(self, global_state):
        global_state.mstate.stack.append(global_state.new_bitvec("msize", 256))
        return [global_state]

    @StateTransition()
    def gas_(self, global_state):
        global_state.mstate.stack.append(global_state.new_bitvec("gas", 256))
        return [global_state]

    @StateTransition()
    def log_(self, global_state):
        # TODO: implement me
        state = global_state.mstate
        dpth = int(self.op_code[3:])
        state.stack.pop(), state.stack.pop()
        [state.stack.pop() for x in range(dpth)]
        # Not supported
        return [global_state]

    @StateTransition()
    def create_(self, global_state):
        # TODO: implement me
        state = global_state.mstate
        state.stack.pop(), state.stack.pop(), state.stack.pop()
        # Not supported
        state.stack.append(0)
        return [global_state]

    @StateTransition()
    def return_(self, global_state):
        state = global_state.mstate
        offset, length = state.stack.pop(), state.stack.pop()
        return_data = [global_state.new_bitvec("return_data", 256)]
        try:
            return_data = state.memory[util.get_concrete_int(offset):util.get_concrete_int(offset + length)]
        except AttributeError:
            logging.debug("Return with symbolic length or offset. Not supported")
        global_state.current_transaction.end(global_state, return_data)

    @StateTransition()
    def suicide_(self, global_state):
        target = global_state.mstate.stack.pop()

        # Often the target of the suicide instruction will be symbolic
        # If it isn't then well transfer the balance to the indicated contract
        if isinstance(target, BitVecNumRef):
            target = '0x' + hex(target.as_long())[-40:]
        if isinstance(target, str):
            try:
                global_state.world_state[target].balance += global_state.environment.active_account.balance
            except KeyError:
                global_state.world_state.create_account(address=target, balance=global_state.environment.active_account.balance)

        global_state.environment.active_account.balance = 0
        global_state.environment.active_account.deleted = True

        global_state.current_transaction.end(global_state)

    @StateTransition()
    def revert_(self, global_state):
        return []

    @StateTransition()
    def assert_fail_(self, global_state):
        # 0xfe: designated invalid opcode
        raise InvalidJumpDestination

    @StateTransition()
    def invalid_(self, global_state):
        raise InvalidJumpDestination

    @StateTransition()
    def stop_(self, global_state):
        global_state.current_transaction.end(global_state)

    @StateTransition()
    def call_(self, global_state):

        instr = global_state.get_current_instruction()
        environment = global_state.environment

        try:
            callee_address, callee_account, call_data, value, call_data_type, gas, memory_out_offset, memory_out_size = get_call_parameters(
                global_state, self.dynamic_loader, True)
        except ValueError as e:
            logging.info(
                "Could not determine required parameters for call, putting fresh symbol on the stack. \n{}".format(e)
            )
            # TODO: decide what to do in this case
            global_state.mstate.stack.append(global_state.new_bitvec("retval_" + str(instr['address']), 256))
            return [global_state]
        global_state.mstate.stack.append(global_state.new_bitvec("retval_" + str(instr['address']), 256))

        if 0 < int(callee_address, 16) < 5:
            logging.info("Native contract called: " + callee_address)
            if call_data == [] and call_data_type == CalldataType.SYMBOLIC:
                logging.debug("CALL with symbolic data not supported")
                return [global_state]

            try:
                mem_out_start = helper.get_concrete_int(memory_out_offset)
                mem_out_sz = memory_out_size.as_long()
            except AttributeError:
                logging.debug("CALL with symbolic start or offset not supported")
                return [global_state]

            global_state.mstate.mem_extend(mem_out_start, mem_out_sz)
            call_address_int = int(callee_address, 16)
            try:
                data = natives.native_contracts(call_address_int, call_data)
            except natives.NativeContractException:
                contract_list = ['ecerecover', 'sha256', 'ripemd160', 'identity']
                for i in range(mem_out_sz):
                    global_state.mstate.memory[mem_out_start + i] = global_state.new_bitvec(contract_list[call_address_int - 1] +
                                                                           "(" + str(call_data) + ")", 256)

                return [global_state]

            for i in range(min(len(data), mem_out_sz)):  # If more data is used then it's chopped off
                global_state.mstate.memory[mem_out_start + i] = data[i]

            # TODO: maybe use BitVec here constrained to 1
            return [global_state]

        transaction = MessageCallTransaction(global_state.world_state,
                                             callee_account,
                                             BitVecVal(int(environment.active_account.address, 16), 256),
                                             call_data=call_data,
                                             gas_price=environment.gasprice,
                                             call_value=value,
                                             origin=environment.origin,
                                             call_data_type=call_data_type)
        raise TransactionStartSignal(transaction, self.op_code)

    @StateTransition()
    def call_post(self, global_state):
        instr = global_state.get_current_instruction()

        try:
            _, _, _, _, _, _, memory_out_offset, memory_out_size = get_call_parameters(
                global_state, self.dynamic_loader, True)
        except ValueError as e:
            logging.info(
                "Could not determine required parameters for call, putting fresh symbol on the stack. \n{}".format(e)
            )
            global_state.mstate.stack.append(global_state.new_bitvec("retval_" + str(instr['address']), 256))
            return [global_state]

        if global_state.last_return_data is None:
            # Put return value on stack
            return_value = global_state.new_bitvec("retval_" + str(instr['address']), 256)
            global_state.mstate.stack.append(return_value)
            global_state.mstate.constraints.append(return_value == 0)

            return [global_state]

        try:
            memory_out_offset = util.get_concrete_int(memory_out_offset) if isinstance(memory_out_offset, ExprRef) else memory_out_offset
            memory_out_size = util.get_concrete_int(memory_out_size) if isinstance(memory_out_size, ExprRef) else memory_out_size
        except AttributeError:
            global_state.mstate.stack.append(global_state.new_bitvec("retval_" + str(instr['address']), 256))
            return [global_state]

        # Copy memory
        global_state.mstate.mem_extend(memory_out_offset, min(memory_out_size, len(global_state.last_return_data)))
        for i in range(min(memory_out_size, len(global_state.last_return_data))):
            global_state.mstate.memory[i + memory_out_offset] = global_state.last_return_data[i]

        # Put return value on stack
        return_value = global_state.new_bitvec("retval_" + str(instr['address']), 256)
        global_state.mstate.stack.append(return_value)
        global_state.mstate.constraints.append(return_value == 1)

        return [global_state]

    @StateTransition()
    def callcode_(self, global_state):
        instr = global_state.get_current_instruction()
        environment = global_state.environment

        try:
            callee_address, callee_account, call_data, value, call_data_type, gas, _, _ = get_call_parameters(
                global_state, self.dynamic_loader, True)
        except ValueError as e:
            logging.info(
                "Could not determine required parameters for call, putting fresh symbol on the stack. \n{}".format(e)
            )
            global_state.mstate.stack.append(global_state.new_bitvec("retval_" + str(instr['address']), 256))
            return [global_state]

        transaction = MessageCallTransaction(global_state.world_state,
                                             environment.active_account,
                                             environment.address,
                                             call_data=call_data,
                                             gas_price=environment.gasprice,
                                             call_value=value,
                                             origin=environment.origin,
                                             call_data_type=call_data_type,
                                             code=callee_account.code
                                             )
        raise TransactionStartSignal(transaction, self.op_code)

    @StateTransition()
    def callcode_post(self, global_state):
        instr = global_state.get_current_instruction()

        try:
            _, _, _, _, _, _, memory_out_offset, memory_out_size = get_call_parameters(
                global_state, self.dynamic_loader, True)
        except ValueError as e:
            logging.info(
                "Could not determine required parameters for call, putting fresh symbol on the stack. \n{}".format(e)
            )
            global_state.mstate.stack.append(global_state.new_bitvec("retval_" + str(instr['address']), 256))
            return [global_state]

        if global_state.last_return_data is None:
            # Put return value on stack
            return_value = global_state.new_bitvec("retval_" + str(instr['address']), 256)
            global_state.mstate.stack.append(return_value)
            global_state.mstate.constraints.append(return_value == 0)

            return [global_state]

        try:
            memory_out_offset = util.get_concrete_int(memory_out_offset) if isinstance(memory_out_offset, ExprRef) else memory_out_offset
            memory_out_size = util.get_concrete_int(memory_out_size) if isinstance(memory_out_size, ExprRef) else memory_out_size
        except AttributeError:
            global_state.mstate.stack.append(global_state.new_bitvec("retval_" + str(instr['address']), 256))
            return [global_state]

        # Copy memory
        global_state.mstate.mem_extend(memory_out_offset, min(memory_out_size, len(global_state.last_return_data)))
        for i in range(min(memory_out_size, len(global_state.last_return_data))):
            global_state.mstate.memory[i + memory_out_offset] = global_state.last_return_data[i]

        # Put return value on stack
        return_value = global_state.new_bitvec("retval_" + str(instr['address']), 256)
        global_state.mstate.stack.append(return_value)
        global_state.mstate.constraints.append(return_value == 1)

        return [global_state]


    @StateTransition()
    def delegatecall_(self, global_state):
        instr = global_state.get_current_instruction()
        environment = global_state.environment

        try:
            callee_address, callee_account, call_data, _, call_data_type, gas, _, _ = get_call_parameters(global_state,
                                                                                                          self.dynamic_loader)
        except ValueError as e:
            logging.info(
                "Could not determine required parameters for call, putting fresh symbol on the stack. \n{}".format(e)
            )
            global_state.mstate.stack.append(global_state.new_bitvec("retval_" + str(instr['address']), 256))
            return [global_state]

        transaction = MessageCallTransaction(global_state.world_state,
                                             environment.active_account,
                                             environment.sender,
                                             call_data,
                                             gas_price=environment.gasprice,
                                             call_value=environment.callvalue,
                                             origin=environment.origin,
                                             call_data_type=call_data_type,
                                             code=callee_account.code
                                             )
        raise TransactionStartSignal(transaction, self.op_code)


    @StateTransition()
    def delegatecall_post(self, global_state):
        instr = global_state.get_current_instruction()

        try:
            _, _, _, _, _, _, memory_out_offset, memory_out_size =\
                get_call_parameters(global_state, self.dynamic_loader)
        except ValueError as e:
            logging.info(
                "Could not determine required parameters for call, putting fresh symbol on the stack. \n{}".format(e)
            )
            global_state.mstate.stack.append(global_state.new_bitvec("retval_" + str(instr['address']), 256))
            return [global_state]

        if global_state.last_return_data is None:
            # Put return value on stack
            return_value = global_state.new_bitvec("retval_" + str(instr['address']), 256)
            global_state.mstate.stack.append(return_value)
            global_state.mstate.constraints.append(return_value == 0)

            return [global_state]

        try:
            memory_out_offset = util.get_concrete_int(memory_out_offset) if isinstance(memory_out_offset,
                                                                                       ExprRef) else memory_out_offset
            memory_out_size = util.get_concrete_int(memory_out_size) if isinstance(memory_out_size,
                                                                                   ExprRef) else memory_out_size
        except AttributeError:
            global_state.mstate.stack.append(global_state.new_bitvec("retval_" + str(instr['address']), 256))
            return [global_state]

            # Copy memory
        global_state.mstate.mem_extend(memory_out_offset,
                                       min(memory_out_size, len(global_state.last_return_data)))
        for i in range(min(memory_out_size, len(global_state.last_return_data))):
            global_state.mstate.memory[i + memory_out_offset] = global_state.last_return_data[i]

        # Put return value on stack
        return_value = global_state.new_bitvec("retval_" + str(instr['address']), 256)
        global_state.mstate.stack.append(return_value)
        global_state.mstate.constraints.append(return_value == 1)

        return [global_state]

    @StateTransition()
    def staticcall_(self, global_state):
        # TODO: implement me
        instr = global_state.get_current_instruction()
        global_state.mstate.stack.append(global_state.new_bitvec("retval_" + str(instr['address']), 256))
        return [global_state]

