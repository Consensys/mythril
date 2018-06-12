from mythril.laser.ethereum import util
from ethereum import utils
from mythril.laser.ethereum.state import CalldataType, GlobalState, MachineState, Environment, Account
from z3 import BitVecVal, BitVec, BoolRef, Extract, If, UDiv, URem, simplify, Concat, ULT, UGT, BitVecNumRef, Not, \
    is_false, is_true, ExprRef
from mythril.laser.ethereum.svm import GlobalState
import mythril.laser.ethereum.util as helper
import ethereum.opcodes as opcodes
from z3 import BitVecVal, If, BoolRef
from copy import copy
import logging
import binascii

TT256 = 2 ** 256
TT256M1 = 2 ** 256 - 1


class StackUnderflowException(Exception):
    pass


class StopSignal(Exception):
    pass


def instruction(func):
    """ Wrapper that handles copy and original return """

    def wrapper(self, global_state):
        new_global_state = copy(global_state)
        new_global_state.mstate.pc += 1
        return global_state, func(self, new_global_state)

    return wrapper


class Instruction:
    """
    Instruction class is used to mutate a state according to the current instruction
    """

    def __init__(self, op_code):
        assert any(lambda opcodes_element: op_code == opcodes_element[0], opcodes.opcodes)
        self.op_code = op_code

    def evaluate(self, global_state):
        """ Performs the mutation for this instruction """

        # Generalize some ops
        op = self.op_code.lower()
        if self.op_code.startswith("PUSH"):
            op = "push"
        elif self.op_code.startswith("DUP"):
            op = "dup"
        elif self.op_code.startswith("SWAP"):
            op = "swap"
        elif self.op_code.startswith("LOG"):
            op = "log"

        instruction_mutator = getattr(self, op + '_', None)

        if instruction_mutator is None:
            raise NotImplemented()

        return instruction_mutator(global_state)

    #TODO: STOP
    @instruction
    def push_(self, global_state):
        value = BitVecVal(int(global_state.get_current_instruction()['argument'][2:], 16), 256)
        global_state.mstate.stack.append(value)
        return [global_state]

    @instruction
    def dup_(self, global_state):
        value = BitVecVal(int(global_state.get_current_instruction()['argument'][2:], 16), 256)
        global_state.mstate.stack.append(value)
        return [global_state]

    @instruction
    def swap_(self, global_state):
        depth = int(self.op_code[4:])
        try:
            stack = global_state.mstate.stack
            stack[-depth - 1], stack[-1] = stack[-1], stack[-depth - 1]
        except IndexError:
            raise StackUnderflowException()
        return [global_state]

    @instruction
    def pop_(self, global_state):
        try:
            global_state.mstate.stack.pop()
        except IndexError:
            raise StackUnderflowException()
        return [global_state]

    @instruction
    def and_(self, global_state):
        try:
            stack = global_state.mstate.stack
            op1, op2 = stack.pop(), stack.pop()
            if type(op1) == BoolRef:
                op1 = If(op1, BitVecVal(1, 256), BitVecVal(0, 256))
            if type(op2) == BoolRef:
                op2 = If(op2, BitVecVal(1, 256), BitVecVal(0, 256))

            stack.append(op1 & op2)
        except IndexError:
            raise StackUnderflowException()
        return [global_state]

    @instruction
    def or_(self, global_state):
        stack = global_state.mstate.stack
        try:
            op1, op2 = stack.pop(), stack.pop()

            if type(op1) == BoolRef:
                op1 = If(op1, BitVecVal(1, 256), BitVecVal(0, 256))

            if type(op2) == BoolRef:
                op2 = If(op2, BitVecVal(1, 256), BitVecVal(0, 256))

            stack.append(op1 | op2)
        except IndexError:  # Stack underflow
            raise StackUnderflowException()
        return [global_state]

    @instruction
    def xor_(self, global_state):
        mstate = global_state.mstate
        mstate.stack.append(mstate.stack.pop() ^ mstate.stack.pop())
        return [global_state]

    @instruction
    def not_(self, global_state: GlobalState):
        mstate = global_state.mstate
        mstate.stack.append(TT256M1 - mstate.stack.pop())
        return [global_state]

    @instruction
    def byte_(self, global_state):
        mstate = global_state.mstate
        op0, op1 = mstate.stack.pop(), mstate.stack.pop()

        try:
            index = util.get_concrete_int(op0)
            offset = (31 - index) * 8
            result = Concat(BitVecVal(0, 248), Extract(offset + 7, offset, op1))
        except AttributeError:
            logging.debug("BYTE: Unsupported symbolic byte offset")
            result = BitVec(str(simplify(op1)) + "_" + str(simplify(op0)), 256)

        mstate.stack.append(simplify(result))
        return [global_state]

    # Arithmetic
    @instruction
    def add_(self, global_state):
        global_state.mstate.stack.append(
            (helper.pop_bitvec(global_state.mstate) + helper.pop_bitvec(global_state.mstate)))
        return [global_state]

    @instruction
    def sub_(self, global_state):
        global_state.mstate.stack.append(
            (helper.pop_bitvec(global_state.mstate) - helper.pop_bitvec(global_state.mstate)))
        return [global_state]

    @instruction
    def mul_(self, global_state):
        global_state.mstate.stack.append(
            (helper.pop_bitvec(global_state.mstate) * helper.pop_bitvec(global_state.mstate)))
        return [global_state]

    @instruction
    def div_(self, global_state):
        global_state.mstate.stack.append(
            UDiv(util.pop_bitvec(global_state.mstate), util.pop_bitvec(global_state.mstate)))
        return [global_state]

    @instruction
    def sdiv_(self, global_state):
        s0, s1 = util.pop_bitvec(global_state.mstate), util.pop_bitvec(global_state.mstate)
        global_state.mstate.stack.append(s0 / s1)
        return [global_state]

    @instruction
    def smod_(self, global_state):
        s0, s1 = util.pop_bitvec(global_state.mstate), util.pop_bitvec(global_state.mstate)
        global_state.mstate.stack.append(0 if s1 == 0 else s0 % s1)
        return [global_state]

    @instruction
    def addmod_(self, global_state):
        s0, s1, s2 = util.pop_bitvec(global_state.mstate), util.pop_bitvec(global_state.mstate), util.pop_bitvec(
            global_state.mstate)
        global_state.mstate.stack.append((s0 + s1) % s2)
        return [global_state]

    @instruction
    def mulmod_(self, global_state):
        s0, s1, s2 = util.pop_bitvec(global_state.mstate), util.pop_bitvec(global_state.mstate), util.pop_bitvec(
            global_state.mstate)
        global_state.mstate.stack.append((s0 * s1) % s2 if s2 else 0)

    @instruction
    def exp_(self, global_state):
        state = global_state.mstate
        # we only implement 2 ** x
        base, exponent = util.pop_bitvec(state), util.pop_bitvec(state)

        if (type(base) != BitVecNumRef) or (type(exponent) != BitVecNumRef):
            state.stack.append(BitVec(str(base) + "_EXP_" + str(exponent), 256))
        elif base.as_long() == 2:
            if exponent.as_long() == 0:
                state.stack.append(BitVecVal(1, 256))
            else:
                state.stack.append(base << (exponent - 1))
        else:
            state.stack.append(base)
        return [global_state]

    @instruction
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
    @instruction
    def lt_(self, global_state):
        state = global_state.mstate
        exp = ULT(util.pop_bitvec(state), util.pop_bitvec(state))
        state.stack.append(exp)
        return [global_state]

    @instruction
    def gt_(self, global_state):
        state = global_state.mstate
        exp = UGT(util.pop_bitvec(state), util.pop_bitvec(state))
        state.stack.append(exp)
        return [global_state]

    @instruction
    def slt_(self, global_state):
        state = global_state.mstate
        exp = util.pop_bitvec(state) < util.pop_bitvec(state)
        state.stack.append(exp)
        return [global_state]

    @instruction
    def sgt_(self, global_state):
        state = global_state.mstate

        exp = util.pop_bitvec(state) > util.pop_bitvec(state)
        state.stack.append(exp)
        return [global_state]

    @instruction
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

    @instruction
    def iszero_(self, global_state):
        state = global_state.mstate

        val = state.stack.pop()
        exp = val is False if type(val) == BoolRef else val == 0
        state.stack.append(exp)

        return [global_state]

    # Call data
    @instruction
    def callvalue_(self, global_state):
        state = global_state.mstate
        environment = global_state.environment
        state.stack.append(environment.callvalue)

        return [global_state]

    @instruction
    def calldataload_(self, global_state):
        state = global_state.mstate
        environment = global_state.environment
        op0 = state.stack.pop()

        try:
            offset = util.get_concrete_int(simplify(op0))
            b = environment.calldata[offset]
        except AttributeError:
            logging.debug("CALLDATALOAD: Unsupported symbolic index")
            state.stack.append(
                BitVec("calldata_" + str(environment.active_account.contract_name) + "_" + str(op0), 256))
            return [global_state]
        except IndexError:
            logging.debug("Calldata not set, using symbolic variable instead")
            state.stack.append(
                BitVec("calldata_" + str(environment.active_account.contract_name) + "_" + str(op0), 256))
            return [global_state]


        if type(b) == int:
            val = b''

            try:
                for i in range(offset, offset + 32):
                    val += environment.calldata[i].to_bytes(1, byteorder='big')

                logging.debug("Final value: " + str(int.from_bytes(val, byteorder='big')))
                state.stack.append(BitVecVal(int.from_bytes(val, byteorder='big'), 256))
            #FIXME: broad exception catch
            except:
                state.stack.append(
                    BitVec("calldata_" + str(environment.active_account.contract_name) + "_" + str(op0), 256))
        else:
            # symbolic variable
            state.stack.append(
                BitVec("calldata_" + str(environment.active_account.contract_name) + "_" + str(op0), 256))

        return [global_state]

    @instruction
    def calldatasize_(self, global_state):
        state = global_state.mstate
        environment = global_state.environment
        if environment.calldata_type == CalldataType.SYMBOLIC:
            state.stack.append(BitVec("calldatasize_" + environment.active_account.contract_name, 256))
        else:
            state.stack.append(BitVecVal(len(environment.calldata), 256))
        return [global_state]

    @instruction
    def calldatacopy_(self, global_state):
        state = global_state.mstate
        environment = global_state.environment
        op0, op1, op2 = state.stack.pop(), state.stack.pop(), state.stack.pop()

        try:
            mstart = util.get_concrete_int(op0)
            #FIXME: broad exception catch
        except:
            logging.debug("Unsupported symbolic memory offset in CALLDATACOPY")
            return [global_state]

        try:
            dstart = util.get_concrete_int(op1)
            #FIXME: broad exception catch
        except:
            logging.debug("Unsupported symbolic calldata offset in CALLDATACOPY")
            state.mem_extend(mstart, 1)
            state.memory[mstart] = BitVec("calldata_" + str(environment.active_account.contract_name) + "_cpy",
                                          256)
            return [global_state]


        try:
            size = util.get_concrete_int(op2)
            #FIXME: broad exception catch
        except:
            logging.debug("Unsupported symbolic size in CALLDATACOPY")
            state.mem_extend(mstart, 1)
            state.memory[mstart] = BitVec(
                "calldata_" + str(environment.active_account.contract_name) + "_" + str(dstart), 256)
            return [global_state]

        if size > 0:
            try:
                state.mem_extend(mstart, size)
            # FIXME: broad exception catch
            except:
                logging.debug("Memory allocation error: mstart = " + str(mstart) + ", size = " + str(size))
                state.mem_extend(mstart, 1)
                state.memory[mstart] = BitVec(
                    "calldata_" + str(environment.active_account.contract_name) + "_" + str(dstart), 256)
                return [global_state]

            try:
                i_data = environment.calldata[dstart]

                for i in range(mstart, mstart + size):
                    state.memory[i] = environment.calldata[i_data]
                    i_data += 1
            except:
                logging.debug("Exception copying calldata to memory")

                state.memory[mstart] = BitVec(
                    "calldata_" + str(environment.active_account.contract_name) + "_" + str(dstart), 256)
        return [global_state]

    # Environment
    @instruction
    def address_(self, global_state):
        state = global_state.mstate
        environment = global_state.environment
        state.stack.append(environment.address)
        return [global_state]

    @instruction
    def balance_(self, global_state):
        state = global_state.mstate
        address = state.stack.pop()
        state.stack.append(BitVec("balance_at_" + str(address), 256))
        return [global_state]

    @instruction
    def origin_(self, global_state):
        state = global_state.mstate
        environment = global_state.environment
        state.stack.append(environment.origin)
        return [global_state]

    @instruction
    def caller_(self, global_state):
        state = global_state.mstate
        environment = global_state.environment
        state.stack.append(environment.sender)
        return [global_state]

    @instruction
    def codesize_(self, global_state):
        state = global_state.mstate
        environment = global_state.environment
        state.stack.append(len(environment.code.instruction_list))
        return [global_state]

    @instruction
    def sha3_(self, global_state):
        state = global_state.mstate
        environment = global_state.environment
        op0, op1 = state.stack.pop(), state.stack.pop()

        try:
            index, length = util.get_concrete_int(op0), util.get_concrete_int(op1)
        # FIXME: broad exception catch
        except:
            # Can't access symbolic memory offsets
            state.stack.append(BitVec("KECCAC_mem_" + str(op0) + ")", 256))
            return [global_state]


        try:
            data = b''

            for i in range(index, index + length):
                data += util.get_concrete_int(state.memory[i]).to_bytes(1, byteorder='big')
                i += 1
            # FIXME: broad exception catch
        except:

            svar = str(state.memory[index])

            svar = svar.replace(" ", "_")

            state.stack.append(BitVec("keccac_" + svar, 256))
            return [global_state]

        keccac = utils.sha3(utils.bytearray_to_bytestr(data))
        logging.debug("Computed SHA3 Hash: " + str(binascii.hexlify(keccac)))

        state.stack.append(BitVecVal(util.concrete_int_from_bytes(keccac, 0), 256))
        return [global_state]

    @instruction
    def gasprice_(self, global_state):
        global_state.mstate.stack.append(BitVec("gasprice", 256))
        return [global_state]

    @instruction
    def codecopy(self, global_state):
        # FIXME: not implemented
        state = global_state.mstate
        start, s1, size = state.stack.pop(), state.stack.pop(), state.stack.pop()
        return [global_state]

    @instruction
    def extcodesize_(self, global_state):
        addr = global_state.mstate.stack.pop()
        global_state.state.stack.append(BitVec("extcodesize", 256))
        return [global_state]

    @instruction
    def extcodecopy_(self, global_state):
        # FIXME: not implemented
        state = global_state.mstate
        addr = state.stack.pop()
        start, s2, size = state.stack.pop(), state.stack.pop(), state.stack.pop()
        return [global_state]

    @instruction
    def returndatasize_(self, global_state):
        global_state.mstate.stack.append(BitVec("returndatasize", 256))
        return[global_state]

    @instruction
    def blockhash_(self, global_state):
        state = global_state.mstate
        blocknumber = state.stack.pop()
        state.stack.append(BitVec("blockhash_block_" + str(blocknumber), 256))
        return global_state

    @instruction
    def coinbase_(self, global_state):
        global_state.mstate.stack.append(BitVec("coinbase", 256))
        return [global_state]

    @instruction
    def timestamp_(self, global_state):
        global_state.mstate.stack.append(BitVec("timestamp", 256))
        return [global_state]

    @instruction
    def number_(self, global_state):
        global_state.mstate.stack.append(BitVec("block_number", 256))
        return [global_state]

    @instruction
    def difficulty_(self, global_state):
        global_state.mstate.stack.append(BitVec("block_difficulty", 256))
        return [global_state]

    @instruction
    def gaslimit_(self, global_state):
        global_state.mstate.stack.append(BitVec("block_gaslimit", 256))
        return [global_state]

    # Memory operations
    @instruction
    def mload_(self, global_state):
        state = global_state.mstate
        op0 = state.stack.pop()

        logging.debug("MLOAD[" + str(op0) + "]")

        try:
            offset = util.get_concrete_int(op0)
        except AttributeError:
            logging.debug("Can't MLOAD from symbolic index")
            data = BitVec("mem_" + str(op0), 256)
            state.stack.append(data)
            return [global_state]

        try:
            data = util.concrete_int_from_bytes(state.memory, offset)
        except IndexError:  # Memory slot not allocated
            data = BitVec("mem_" + str(offset), 256)
        except TypeError:  # Symbolic memory
            data = state.memory[offset]

        logging.debug("Load from memory[" + str(offset) + "]: " + str(data))

        state.stack.append(data)
        return [global_state]

    @instruction
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

    @instruction
    def _mstore8(self, global_state):
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

    @instruction
    def _sload(self, global_state):
        state = global_state.mstate
        index = state.stack.pop()
        logging.debug("Storage access at index " + str(index))

        try:
            index = util.get_concrete_int(index)
        except AttributeError:
            index = str(index)

        try:
            data = global_state.environment.active_account.storage[index]
        except KeyError:
            data = BitVec("storage_" + str(index), 256)
            global_state.environment.active_account.storage[index] = data

        state.stack.append(data)
        return [global_state]

    @instruction
    def sstore_(self, global_state):
        state = global_state.mstate
        index, value = state.stack.pop(), state.stack.pop()

        logging.debug("Write to storage[" + str(index) + "]")

        try:
            index = util.get_concrete_int(index)
        except AttributeError:
            index = str(index)

        try:
            # Create a fresh copy of the account object before modifying storage

            for k in global_state.accounts:
                if global_state.accounts[k] == global_state.environment.active_account:
                    global_state.accounts[k] = copy.deepcopy(global_state.accounts[k])
                    global_state.environment.active_account = global_state.accounts[k]
                    break

            global_state.environment.active_account.storage[index] = value
        except KeyError:
            logging.debug("Error writing to storage: Invalid index")
        return [global_state]


    @instruction
    def jump_(self, global_state):
        state = global_state.mstate
        disassembly = global_state.environment.disassembly
        try:
            jump_addr = util.get_concrete_int(state.stack.pop())
        except AttributeError:
            logging.debug("Invalid jump argument (symbolic address)")
            return []
        except IndexError:  # Stack Underflow
            return []

        index = util.get_instruction_index(disassembly.instruction_list, jump_addr)
        if index is None:
            logging.debug("JUMP to invalid address")
            return []

        op_code = disassembly.instruction_list[index]['opcode']

        if op_code != "JUMPDEST":
            logging.debug("Skipping JUMP to invalid destination (not JUMPDEST): " + str(jump_addr))
            return []

        new_state = copy(global_state)
        new_state.mstate.pc = index
        new_state.mstate.depth += 1

        # TODO: create new node
        # self.nodes[new_node.uid] = new_node
        # self.edges.append(Edge(node.uid, new_node.uid, JumpType.UNCONDITIONAL))

        return [new_state]

    def jumpi_(self, global_state):
        state = global_state.mstate
        disassembly = global_state.environment.disassembly
        states = []

        op0, condition = state.stack.pop(), state.stack.pop()

        try:
            jump_addr = util.get_concrete_int(op0)
        # FIXME: to broad exception handler
        except:
            logging.debug("Skipping JUMPI to invalid destination.")
            return [global_state]

        index = util.get_instruction_index(disassembly.instruction_list, jump_addr)

        if not index:
            logging.debug("Invalid jump destination: " + str(jump_addr))
            return [global_state]
        instr = disassembly.instruction_list[index]

        # True case
        condi = condition if type(condition) == BoolRef else condition != 0
        if instr['opcode'] == "JUMPDEST":
            if not is_false(simplify(condi)):
                new_state = copy(global_state)
                new_state.mstate.pc = index
                new_state.mstate.depth += 1
                new_state.mstate.constraints.append(condi)

                # TODO: create new node
                # self.nodes[new_node.uid] = new_node
                # self.edges.append(Edge(node.uid, new_node.uid, JumpType.CONDITIONAL, condi))
                states.append(new_state)
            else:
                logging.debug("Pruned unreachable states.")

        # False case
        negated = Not(condition) if type(condition) == BoolRef else condition == 0

        if not is_false(simplify(negated)):
            new_state = copy(global_state)
            new_state.mstate.pc = index
            new_state.mstate.depth += 1
            new_state.mstate.constraints.append(negated)
            states.append(new_state)
            # TODO: create new node
            # self.nodes[new_node.uid] = new_node
            # self.edges.append(Edge(node.uid, new_node.uid, JumpType.CONDITIONAL, negated))
        else:
            logging.debug("Pruned unreachable states.")

        return states
