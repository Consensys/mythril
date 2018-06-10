from mythril.laser.ethereum import util
from ethereum import utils
from enum import Enum
from z3 import *
import binascii
import copy
import logging
import re
from mythril.laser.ethereum.state import *
from mythril.laser.ethereum.cfg import *
TT256 = 2 ** 256
TT256M1 = 2 ** 256 - 1

gbl_next_uid = 0  # node counter


class CalldataType(Enum):
    CONCRETE = 1
    SYMBOLIC = 2


class SVMError(Exception):
    pass


'''
Main symbolic execution engine.
'''


class LaserEVM:

    def __init__(self, accounts, dynamic_loader=None, max_depth=12):
        self.accounts = accounts
        self.nodes = {}
        self.edges = []
        self.current_func = ""
        self.call_stack = []
        self.pending_returns = {}
        self.total_states = 0
        self.dynamic_loader = dynamic_loader
        self.max_depth = max_depth

        logging.info("LASER EVM initialized with dynamic loader: " + str(dynamic_loader))

    @staticmethod
    def copy_global_state(gblState):
        mstate = copy.deepcopy(gblState.mstate)
        environment = copy.copy(gblState.environment)
        accounts = copy.copy(gblState.accounts)

        return GlobalState(accounts, environment, mstate)

    def sym_exec(self, main_address):

        logging.debug("Starting LASER execution")

        # Initialize the execution environment

        environment = Environment(
            self.accounts[main_address],
            BitVec("caller", 256),
            [],
            BitVec("gasprice", 256),
            BitVec("callvalue", 256),
            BitVec("origin", 256),
            calldata_type=CalldataType.SYMBOLIC,
        )

        gblState = GlobalState(self.accounts, environment)

        node = self._sym_exec(gblState)
        self.nodes[node.uid] = node
        logging.info("Execution complete")
        logging.info("%d nodes, %d edges, %d total states", len(self.nodes), len(self.edges), self.total_states)

    def _sym_exec(self, gblState):

        environment = gblState.environment
        disassembly = environment.code
        state = gblState.mstate

        start_addr = disassembly.instruction_list[state.pc]['address']

        node = Node(environment.active_account.contract_name, start_addr, copy.deepcopy(state.constraints))

        if start_addr == 0:
            environment.active_function_name = "fallback"

        logging.debug("- Entering node " + str(node.uid) + ", index = " + str(state.pc) + ", address = " + str(start_addr) + ", depth = " + str(state.depth))

        if start_addr in disassembly.addr_to_func:
            # Enter a new function

            environment.active_function_name = disassembly.addr_to_func[start_addr]
            node.flags |= NodeFlags.FUNC_ENTRY

            logging.info("- Entering function " + environment.active_account.contract_name + ":" + node.function_name)

        node.function_name = environment.active_function_name

        halt = False

        while not halt:

            try:
                instr = disassembly.instruction_list[state.pc]
            except IndexError:
                logging.debug("Invalid PC")
                return node

            # Save state before modifying anything

            node.states.append(gblState)
            gblState = LaserEVM.copy_global_state(gblState)

            state = gblState.mstate

            self.total_states += 1

            # Point program counter to next instruction

            state.pc += 1
            op = instr['opcode']

            # logging.debug("[" + environment.active_account.contract_name + "] " + helper.get_trace_line(instr, state))
            # slows down execution significantly.

            # Stack ops

            if op.startswith("PUSH"):
                value = BitVecVal(int(instr['argument'][2:], 16), 256)
                state.stack.append(value)

            elif op.startswith('DUP'):
                dpth = int(op[3:])

                try:
                    state.stack.append(state.stack[-dpth])
                except:
                    halt = True

            elif op.startswith('SWAP'):

                dpth = int(op[4:])

                try:
                    temp = state.stack[-dpth - 1]

                    state.stack[-dpth - 1] = state.stack[-1]
                    state.stack[-1] = temp
                except IndexError:  # Stack underflow
                    halt = True

            elif op == 'POP':
                try:
                    state.stack.pop()
                except IndexError:  # Stack underflow
                    halt = True

            # Bitwise ops

            elif op == 'AND':
                try:
                    op1, op2 = state.stack.pop(), state.stack.pop()
                    if (type(op1) == BoolRef):
                        op1 = If(op1, BitVecVal(1, 256), BitVecVal(0, 256))

                    if (type(op2) == BoolRef):
                        op2 = If(op2, BitVecVal(1, 256), BitVecVal(0, 256))

                    state.stack.append(op1 & op2)
                except IndexError:  # Stack underflow
                    halt = True

            elif op == 'OR':
                try:
                    op1, op2 = state.stack.pop(), state.stack.pop()

                    if (type(op1) == BoolRef):
                        op1 = If(op1, BitVecVal(1, 256), BitVecVal(0, 256))

                    if (type(op2) == BoolRef):
                        op2 = If(op2, BitVecVal(1, 256), BitVecVal(0, 256))

                    state.stack.append(op1 | op2)
                except IndexError:  # Stack underflow
                    halt = True

            elif op == 'XOR':
                state.stack.append(state.stack.pop() ^ state.stack.pop())

            elif op == 'NOT':
                state.stack.append(TT256M1 - state.stack.pop())

            elif op == 'BYTE':
                s0, s1 = state.stack.pop(), state.stack.pop()

                try:
                    n = util.get_concrete_int(s0)
                    oft = (31 - n) * 8
                    result = Concat(BitVecVal(0, 248), Extract(oft + 7, oft, s1))
                except AttributeError:
                    logging.debug("BYTE: Unsupported symbolic byte offset")
                    result = BitVec(str(simplify(s1)) + "_" + str(simplify(s0)), 256)

                state.stack.append(simplify(result))

            # Arithmetics

            elif op == 'ADD':
                state.stack.append((util.pop_bitvec(state) + util.pop_bitvec(state)))

            elif op == 'SUB':
                state.stack.append((util.pop_bitvec(state) - util.pop_bitvec(state)))

            elif op == 'MUL':
                state.stack.append(util.pop_bitvec(state) * util.pop_bitvec(state))

            elif op == 'DIV':
                state.stack.append(UDiv(util.pop_bitvec(state), util.pop_bitvec(state)))

            elif op == 'MOD':
                s0, s1 = util.pop_bitvec(state), util.pop_bitvec(state)
                state.stack.append(0 if s1 == 0 else URem(s0, s1))

            elif op == 'SDIV':
                s0, s1 = util.pop_bitvec(state), util.pop_bitvec(state)
                state.stack.append(s0 / s1)

            elif op == 'SMOD':
                s0, s1 = util.pop_bitvec(state), util.pop_bitvec(state)
                state.stack.append(0 if s1 == 0 else s0 % s1)

            elif op == 'ADDMOD':
                s0, s1, s2 = util.pop_bitvec(state), util.pop_bitvec(state), util.pop_bitvec(state)

                logging.info(str(type))

                state.stack.append((s0 + s1) % s2)

            elif op == 'MULMOD':
                s0, s1, s2 = util.pop_bitvec(state), util.pop_bitvec(state), util.pop_bitvec(state)
                state.stack.append((s0 * s1) % s2 if s2 else 0)

            elif op == 'EXP':
                # we only implement 2 ** x
                base, exponent = util.pop_bitvec(state), util.pop_bitvec(state)

                if (type(base) != BitVecNumRef) or (type(exponent) != BitVecNumRef):
                    state.stack.append(BitVec(str(base) + "_EXP_" + str(exponent), 256))
                elif (base.as_long() == 2):
                    if exponent.as_long() == 0:
                        state.stack.append(BitVecVal(1, 256))
                    else:
                        state.stack.append(base << (exponent - 1))

                else:
                    state.stack.append(base)

            elif op == 'SIGNEXTEND':
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
                except:
                    halt = True
                    continue

            # Comparisons

            elif op == 'LT':

                exp = ULT(util.pop_bitvec(state), util.pop_bitvec(state))
                state.stack.append(exp)

            elif op == 'GT':

                exp = UGT(util.pop_bitvec(state), util.pop_bitvec(state))
                state.stack.append(exp)

            elif op == 'SLT':

                exp = util.pop_bitvec(state) < util.pop_bitvec(state)
                state.stack.append(exp)

            elif op == 'SGT':

                exp = util.pop_bitvec(state) > util.pop_bitvec(state)
                state.stack.append(exp)

            elif op == 'EQ':

                op1 = state.stack.pop()
                op2 = state.stack.pop()

                if(type(op1) == BoolRef):
                    op1 = If(op1, BitVecVal(1, 256), BitVecVal(0, 256))

                if(type(op2) == BoolRef):
                    op2 = If(op2, BitVecVal(1, 256), BitVecVal(0, 256))

                exp = op1 == op2

                state.stack.append(exp)

            elif op == 'ISZERO':

                val = state.stack.pop()

                if (type(val) == BoolRef):
                    exp = val == False
                else:
                    exp = val == 0

                state.stack.append(exp)

            # Call data

            elif op == 'CALLVALUE':
                state.stack.append(environment.callvalue)

            elif op == 'CALLDATALOAD':
                # unpack 32 bytes from calldata into a word and put it on the stack

                op0 = state.stack.pop()

                try:
                    offset = util.get_concrete_int(simplify(op0))
                    b = environment.calldata[offset]

                except AttributeError:
                    logging.debug("CALLDATALOAD: Unsupported symbolic index")
                    state.stack.append(BitVec("calldata_" + str(environment.active_account.contract_name) + "_" + str(op0), 256))
                    continue
                except IndexError:
                    logging.debug("Calldata not set, using symbolic variable instead")
                    state.stack.append(BitVec("calldata_" + str(environment.active_account.contract_name) + "_" + str(op0), 256))
                    continue

                if type(b) == int:

                    val = b''

                    try:
                        for i in range(offset, offset + 32):
                            val += environment.calldata[i].to_bytes(1, byteorder='big')

                        logging.debug("Final value: " + str(int.from_bytes(val, byteorder='big')))
                        state.stack.append(BitVecVal(int.from_bytes(val, byteorder='big'), 256))

                    except:
                        state.stack.append(BitVec("calldata_" + str(environment.active_account.contract_name) + "_" + str(op0), 256))
                else:
                    # symbolic variable
                    state.stack.append(BitVec("calldata_" + str(environment.active_account.contract_name) + "_" + str(op0), 256))

            elif op == 'CALLDATASIZE':

                if environment.calldata_type == CalldataType.SYMBOLIC:
                    state.stack.append(BitVec("calldatasize_" + environment.active_account.contract_name, 256))
                else:
                    state.stack.append(BitVecVal(len(environment.calldata), 256))

            elif op == 'CALLDATACOPY':
                op0, op1, op2 = state.stack.pop(), state.stack.pop(), state.stack.pop()

                try:
                    mstart = util.get_concrete_int(op0)
                except:
                    logging.debug("Unsupported symbolic memory offset in CALLDATACOPY")
                    continue

                try:
                    dstart = util.get_concrete_int(op1)
                except:
                    logging.debug("Unsupported symbolic calldata offset in CALLDATACOPY")
                    state.mem_extend(mstart, 1)
                    state.memory[mstart] = BitVec("calldata_" + str(environment.active_account.contract_name) + "_cpy", 256)
                    continue

                try:
                    size = util.get_concrete_int(op2)
                except:
                    logging.debug("Unsupported symbolic size in CALLDATACOPY")
                    state.mem_extend(mstart, 1)
                    state.memory[mstart] = BitVec("calldata_" + str(environment.active_account.contract_name) + "_" + str(dstart), 256)
                    continue

                if size > 0:

                    try:
                        state.mem_extend(mstart, size)
                    except:
                        logging.debug("Memory allocation error: mstart = " + str(mstart) + ", size = " + str(size))
                        state.mem_extend(mstart, 1)
                        state.memory[mstart] = BitVec("calldata_" + str(environment.active_account.contract_name) + "_" + str(dstart), 256)
                        continue

                    try:
                        i_data = environment.calldata[dstart]

                        for i in range(mstart, mstart + size):
                            state.memory[i] = environment.calldata[i_data]
                            i_data += 1
                    except:
                        logging.debug("Exception copying calldata to memory")

                        state.memory[mstart] = BitVec("calldata_" + str(environment.active_account.contract_name) + "_" + str(dstart), 256)

            elif op == 'STOP':
                if len(self.call_stack):
                    self.pending_returns[self.call_stack[-1]].append(node.uid)

                halt = True
                continue

            # Environment

            elif op == 'ADDRESS':
                state.stack.append(environment.address)

            elif op == 'BALANCE':
                addr = state.stack.pop()
                state.stack.append(BitVec("balance_at_" + str(addr), 256))

            elif op == 'ORIGIN':
                state.stack.append(environment.origin)

            elif op == 'CALLER':
                state.stack.append(environment.sender)

            elif op == 'CODESIZE':
                state.stack.append(len(disassembly.instruction_list))

            if op == 'SHA3':
                op0, op1 = state.stack.pop(), state.stack.pop()

                try:
                    index, length = util.get_concrete_int(op0), util.get_concrete_int(op1)

                except:
                    # Can't access symbolic memory offsets
                    state.stack.append(BitVec("KECCAC_mem_" + str(op0) + ")", 256))
                    continue

                try:
                    data = b''

                    for i in range(index, index + length):
                        data += util.get_concrete_int(state.memory[i]).to_bytes(1, byteorder='big')
                        i += 1
                except:

                    svar = str(state.memory[index])

                    svar = svar.replace(" ", "_")

                    state.stack.append(BitVec("keccac_" + svar, 256))
                    continue

                keccac = utils.sha3(utils.bytearray_to_bytestr(data))
                logging.debug("Computed SHA3 Hash: " + str(binascii.hexlify(keccac)))

                state.stack.append(BitVecVal(util.concrete_int_from_bytes(keccac, 0), 256))

            elif op == 'GASPRICE':
                state.stack.append(BitVec("gasprice", 256))

            elif op == 'CODECOPY':
                # Not implemented
                start, s1, size = state.stack.pop(), state.stack.pop(), state.stack.pop()

            elif op == 'EXTCODESIZE':
                addr = state.stack.pop()
                state.stack.append(BitVec("extcodesize", 256))

            elif op == 'EXTCODECOPY':
                # Not implemented

                addr = state.stack.pop()
                start, s2, size = state.stack.pop(), state.stack.pop(), state.stack.pop()

            elif op == 'RETURNDATASIZE':
                state.stack.append(BitVec("returndatasize", 256))

            elif op == 'BLOCKHASH':
                blocknumber = state.stack.pop()
                state.stack.append(BitVec("blockhash_block_" + str(blocknumber), 256))

            elif op == 'COINBASE':
                state.stack.append(BitVec("coinbase", 256))

            elif op == 'TIMESTAMP':
                state.stack.append(BitVec("timestamp", 256))

            elif op == 'NUMBER':
                state.stack.append(BitVec("block_number", 256))

            elif op == 'DIFFICULTY':
                state.stack.append(BitVec("block_difficulty", 256))

            elif op == 'GASLIMIT':
                state.stack.append(BitVec("block_gaslimit", 256))

            elif op == 'MLOAD':

                op0 = state.stack.pop()

                logging.debug("MLOAD[" + str(op0) + "]")

                try:
                    offset = util.get_concrete_int(op0)
                except AttributeError:
                    logging.debug("Can't MLOAD from symbolic index")
                    data = BitVec("mem_" + str(op0), 256)
                    state.stack.append(data)
                    continue

                try:
                    data = util.concrete_int_from_bytes(state.memory, offset)
                except IndexError:  # Memory slot not allocated
                    data = BitVec("mem_" + str(offset), 256)
                except TypeError:  # Symbolic memory
                    data = state.memory[offset]

                logging.debug("Load from memory[" + str(offset) + "]: " + str(data))

                state.stack.append(data)

            elif op == 'MSTORE':

                op0, value = state.stack.pop(), state.stack.pop()

                try:
                    mstart = util.get_concrete_int(op0)
                except AttributeError:
                    logging.debug("MSTORE to symbolic index. Not supported")
                    continue

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
                        continue

            elif op == 'MSTORE8':
                op0, value = state.stack.pop(), state.stack.pop()

                try:
                    offset = util.get_concrete_int(op0)
                except AttributeError:
                    logging.debug("MSTORE to symbolic index. Not supported")
                    continue

                state.mem_extend(offset, 1)

                state.memory[offset] = value % 256

            elif op == 'SLOAD':
                index = state.stack.pop()
                logging.debug("Storage access at index " + str(index))

                try:
                    index = util.get_concrete_int(index)
                except AttributeError:
                    index = str(index)

                try:
                    data = gblState.environment.active_account.storage[index]
                except KeyError:
                    data = BitVec("storage_" + str(index), 256)
                    gblState.environment.active_account.storage[index] = data

                state.stack.append(data)

            elif op == 'SSTORE':
                index, value = state.stack.pop(), state.stack.pop()

                logging.debug("Write to storage[" + str(index) + "] at node " + str(start_addr))

                try:
                    index = util.get_concrete_int(index)
                except AttributeError:
                    index = str(index)

                try:
                    # Create a fresh copy of the account object before modifying storage

                    for k in gblState.accounts:
                        if gblState.accounts[k] == gblState.environment.active_account:
                            gblState.accounts[k] = copy.deepcopy(gblState.accounts[k])
                            gblState.environment.active_account = gblState.accounts[k]
                            break

                    gblState.environment.active_account.storage[index] = value
                except KeyError:
                    logging.debug("Error writing to storage: Invalid index")
                    continue

            elif op == 'JUMP':

                try:
                    jump_addr = util.get_concrete_int(state.stack.pop())
                except AttributeError:
                    logging.debug("Invalid jump argument (symbolic address)")
                    halt = True
                    continue
                except IndexError:  # Stack Underflow
                    halt = True
                    continue

                if (state.depth < self.max_depth):

                    i = util.get_instruction_index(disassembly.instruction_list, jump_addr)

                    if i is None:
                        logging.debug("JUMP to invalid address")
                        halt = True
                        continue

                    opcode = disassembly.instruction_list[i]['opcode']

                    if opcode == "JUMPDEST":

                        new_gblState = LaserEVM.copy_global_state(gblState)
                        new_gblState.mstate.pc = i
                        new_gblState.mstate.depth += 1

                        new_node = self._sym_exec(new_gblState)
                        self.nodes[new_node.uid] = new_node

                        self.edges.append(Edge(node.uid, new_node.uid, JumpType.UNCONDITIONAL))
                        halt = True
                        continue

                    else:
                        logging.debug("Skipping JUMP to invalid destination (not JUMPDEST): " + str(jump_addr))
                        halt = True
                        # continue
                else:
                    logging.debug("Max depth reached, skipping JUMP")
                    halt = True
                    # continue

            elif op == 'JUMPI':
                op0, condition = state.stack.pop(), state.stack.pop()

                try:
                    jump_addr = util.get_concrete_int(op0)
                except:
                    logging.debug("Skipping JUMPI to invalid destination.")

                if state.depth >= self.max_depth:
                    logging.debug("Max depth reached, skipping JUMPI")
                    halt = True
                    continue

                i = util.get_instruction_index(disassembly.instruction_list, jump_addr)

                if not i:
                    logging.debug("Invalid jump destination: " + str(jump_addr))
                    continue
                instr = disassembly.instruction_list[i]

                # True case
                condi = condition if type(condition) == BoolRef else condition != 0
                if instr['opcode'] == "JUMPDEST":
                    if not is_false(simplify(condi)):
                        new_gblState = LaserEVM.copy_global_state(gblState)
                        new_gblState.mstate.pc = i
                        new_gblState.mstate.constraints.append(condi)
                        new_gblState.mstate.depth += 1

                        new_node = self._sym_exec(new_gblState)
                        self.nodes[new_node.uid] = new_node
                        self.edges.append(Edge(node.uid, new_node.uid, JumpType.CONDITIONAL, condi))
                    else:
                        logging.debug("Pruned unreachable states.")

                # False case
                negated = Not(condition) if type(condition) == BoolRef else condition == 0

                if not is_false(simplify(negated)):
                    new_gblState = LaserEVM.copy_global_state(gblState)
                    new_gblState.mstate.constraints.append(negated)

                    new_node = self._sym_exec(new_gblState)
                    self.nodes[new_node.uid] = new_node
                    self.edges.append(Edge(node.uid, new_node.uid, JumpType.CONDITIONAL, negated))
                else:
                    logging.debug("Pruned unreachable states.")

                halt = True

            elif op == 'PC':
                state.stack.append(state.pc - 1)

            elif op == 'MSIZE':
                state.stack.append(BitVec("msize", 256))

            elif op == 'GAS':
                state.stack.append(BitVec("gas", 256))

            elif op.startswith('LOG'):
                dpth = int(op[3:])
                state.stack.pop(), state.stack.pop()
                [state.stack.pop() for x in range(dpth)]
                # Not supported

            elif op == 'CREATE':
                state.stack.pop(), state.stack.pop(), state.stack.pop()
                # Not supported
                state.stack.append(0)

            elif op in ('CALL', 'CALLCODE', 'DELEGATECALL', 'STATICCALL'):

                if op in ('CALL', 'CALLCODE'):
                    gas, to, value, meminstart, meminsz, memoutstart, memoutsz = \
                        state.stack.pop(), state.stack.pop(), state.stack.pop(), state.stack.pop(), state.stack.pop(), state.stack.pop(), state.stack.pop()

                else:
                    gas, to, meminstart, meminsz, memoutstart, memoutsz = \
                        state.stack.pop(), state.stack.pop(), state.stack.pop(), state.stack.pop(), state.stack.pop(), state.stack.pop()

                try:
                    callee_address = hex(util.get_concrete_int(to))

                except AttributeError:
                    # Not a concrete call address. Call target may be an address in storage.

                    m = re.search(r'storage_(\d+)', str(simplify(to)))

                    logging.debug("CALL to: " + str(simplify(to)))

                    if (m and self.dynamic_loader is not None):
                        idx = int(m.group(1))
                        logging.info("Dynamic contract address at storage index " + str(idx))

                        # attempt to read the contract address from instance storage

                        try:
                            callee_address = self.dynamic_loader.read_storage(environment.active_account.address, idx)
                        except:
                            logging.debug("Error accessing contract storage.")
                            ret = BitVec("retval_" + str(instr['address']), 256)
                            state.stack.append(ret)
                            continue

                        # testrpc simply returns the address, geth response is more elaborate.

                        if not re.match(r"^0x[0-9a-f]{40}$", callee_address):

                            callee_address = "0x" + callee_address[26:]

                    else:
                        ret = BitVec("retval_" + str(instr['address']), 256)
                        state.stack.append(ret)
                        # Set output memory
                        logging.debug("memoutstart: "+ str(memoutstart))
                        if not isinstance(memoutstart, ExprRef):
                            state.mem_extend(memoutstart, 1)
                            state.memory[memoutstart] = ret
                        else:
                            logging.debug("Unsupported memory symbolic index")
                        continue

                if not re.match(r"^0x[0-9a-f]{40}", callee_address):
                        logging.debug("Invalid address: " + str(callee_address))
                        ret = BitVec("retval_" + str(instr['address']), 256)
                        state.stack.append(ret)
                        continue

                if (int(callee_address, 16) < 5):

                    logging.info("Native contract called: " + callee_address)

                    # Todo: Implement native contracts

                    ret = BitVec("retval_" + str(instr['address']), 256)
                    state.stack.append(ret)
                    continue

                try:

                    callee_account = self.accounts[callee_address]

                except KeyError:
                    # We have a valid call address, but contract is not in the modules list

                    logging.info("Module with address " + callee_address + " not loaded.")

                    if self.dynamic_loader is not None:

                        logging.info("Attempting to load dependency")

                        try:
                            code = self.dynamic_loader.dynld(environment.active_account.address, callee_address)
                        except Exception as e:
                            logging.info("Unable to execute dynamic loader.")

                        if code is None:

                            logging.info("No code returned, not a contract account?")
                            ret = BitVec("retval_" + str(instr['address']), 256)
                            state.stack.append(ret)
                            continue

                        # New contract bytecode loaded successfully, create a new contract account

                        self.accounts[callee_address] = Account(callee_address, code, callee_address)

                        logging.info("Dependency loaded: " + callee_address)

                    else:
                        logging.info("Dynamic loader unavailable. Skipping call")
                        ret = BitVec("retval_" + str(instr['address']), 256)
                        state.stack.append(ret)
                        continue

                logging.info("Executing " + op + " to: " + callee_address)

                try:
                    callee_account = self.accounts[callee_address]
                except KeyError:
                    logging.info("Contract " + str(callee_address) + " not loaded.")
                    logging.info((str(self.accounts)))

                    ret = BitVec("retval_" + str(instr['address']), 256)
                    state.stack.append(ret)
                    continue

                try:
                    # TODO: This only allows for either fully concrete or fully symbolic calldata.
                    # Improve management of memory and callata to support a mix between both types.

                    calldata = state.memory[util.get_concrete_int(meminstart):util.get_concrete_int(meminstart + meminsz)]

                    if (len(calldata) < 32):
                        calldata += [0] * (32 - len(calldata))

                    calldata_type = CalldataType.CONCRETE
                    logging.debug("Calldata: " + str(calldata))

                except AttributeError:

                    logging.info("Unsupported symbolic calldata offset")
                    calldata_type = CalldataType.SYMBOLIC
                    calldata = []

                self.call_stack.append(instr['address'])
                self.pending_returns[instr['address']] = []

                if (op == 'CALL'):

                    callee_environment = Environment(callee_account, BitVecVal(int(environment.active_account.address, 16), 256), calldata, environment.gasprice, value, environment.origin, calldata_type=calldata_type)
                    new_gblState = GlobalState(gblState.accounts, callee_environment, MachineState(gas))
                    new_gblState.mstate.depth = state.depth + 1
                    new_gblState.mstate.constraints = copy.deepcopy(state.constraints)

                    new_node = self._sym_exec(new_gblState)

                    self.nodes[new_node.uid] = new_node

                elif (op == 'CALLCODE'):

                    temp_callvalue = environment.callvalue
                    temp_caller = environment.caller
                    temp_calldata = environment.calldata

                    environment.callvalue = value
                    environment.caller = environment.address
                    environment.calldata = calldata

                    new_gblState = GlobalState(gblState.accounts, environment, MachineState(gas))
                    new_gblState.mstate.depth = state.depth + 1
                    new_gblState.mstate.constraints = copy.deepcopy(state.constraints)

                    new_node = self._sym_exec(new_gblState)
                    self.nodes[new_node.uid] = new_node

                    environment.callvalue = temp_callvalue
                    environment.caller = temp_caller
                    environment.calldata = temp_calldata

                elif (op == 'DELEGATECALL'):
                    temp_code = environment.code
                    temp_calldata = environment.calldata

                    environment.code = callee_account.code
                    environment.calldata = calldata

                    new_gblState = GlobalState(gblState.accounts, environment, MachineState(gas))
                    new_gblState.mstate.depth = state.depth + 1
                    new_gblState.mstate.constraints = copy.deepcopy(state.constraints)

                    new_node = self._sym_exec(new_gblState)
                    self.nodes[new_node.uid] = new_node

                    environment.code = temp_code
                    environment.calldata = temp_calldata

                self.edges.append(Edge(node.uid, new_node.uid, JumpType.CALL))

                '''
                There may be multiple possible returns from the callee contract. Currently, we don't create separate nodes on the CFG
                for each of them. Instead, a single "return node" is created and a separate edge is added for each return path.
                The return value is always symbolic.
                '''

                ret = BitVec("retval_" + str(disassembly.instruction_list[state.pc]['address']), 256)
                state.stack.append(ret)

                return_address = self.call_stack.pop()

                new_gblState = LaserEVM.copy_global_state(gblState)
                new_gblState.mstate.depth += 1
                new_node = self._sym_exec(new_gblState)

                new_node.flags |= NodeFlags.CALL_RETURN

                self.nodes[new_node.uid] = new_node

                for ret_uid in self.pending_returns[return_address]:
                    self.edges.append(Edge(ret_uid, new_node.uid, JumpType.RETURN))

                state.stack.append(BitVec("retval", 256))

                halt = True

            elif op == 'RETURN':
                offset, length = state.stack.pop(), state.stack.pop()

                try:
                    self.last_returned = state.memory[util.get_concrete_int(offset):util.get_concrete_int(offset + length)]
                except AttributeError:
                    logging.debug("Return with symbolic length or offset. Not supported")

                if len(self.call_stack):
                    self.pending_returns[self.call_stack[-1]].append(node.uid)

                halt = True

            elif op == 'SUICIDE':
                halt = True

            elif op == 'REVERT':
                if len(self.call_stack):
                    self.pending_returns[self.call_stack[-1]].append(node.uid)

                halt = True

            elif op == 'ASSERT_FAIL' or op == 'INVALID':
                if len(self.call_stack):
                    self.pending_returns[self.call_stack[-1]].append(node.uid)

                halt = True

        logging.debug("Returning from node " + str(node.uid))
        return node
