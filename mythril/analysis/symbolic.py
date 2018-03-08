from mythril import ether
from laser.ethereum import svm
import copy
from .ops import *


class StateSpace:

    '''
    Symbolic EVM wrapper
    '''

    def __init__(self, contracts, dynloader=None, max_depth=12):

        self.accounts = {}

        idx = 0

        for contract in contracts:
            address = ether.util.get_indexed_address(idx)
            self.accounts[address] = svm.Account(address, contract.get_disassembly(), contract.name)
            idx += 1

        self.laser = svm.LaserEVM(self.accounts, dynamic_loader=dynloader, max_depth=max_depth)
        self.laser.sym_exec(ether.util.get_indexed_address(0))

        # self.modules = modules

        self.nodes = self.laser.nodes
        self.edges = self.laser.edges

        # Some pre-analysis

        self.calls = []
        self.sstors = {}

        for key in self.nodes:

            state_index = 0

            for state in self.nodes[key].states:

                instruction = state.get_current_instruction()

                op = instruction['opcode']

                if op in ('CALL', 'CALLCODE', 'DELEGATECALL', 'STATICCALL'):

                    stack = copy.deepcopy(state.mstate.stack)

                    if op in ('CALL', 'CALLCODE'):
                        gas, to, value, meminstart, meminsz, memoutstart, memoutsz = \
                            get_variable(stack.pop()), get_variable(stack.pop()), get_variable(stack.pop()), get_variable(stack.pop()), get_variable(stack.pop()), get_variable(stack.pop()), get_variable(stack.pop())

                        if (to.type == VarType.CONCRETE):
                            if (to.val < 5):
                                # ignore prebuilts
                                continue

                        if (meminstart.type == VarType.CONCRETE and meminsz.type == VarType.CONCRETE):
                            self.calls.append(Call(self.nodes[key], state, state_index, op, to, gas, value, state.mstate.memory[meminstart.val:meminsz.val * 4]))
                        else:
                            self.calls.append(Call(self.nodes[key], state, state_index, op, to, gas, value))
                    else:
                        gas, to, meminstart, meminsz, memoutstart, memoutsz = \
                            get_variable(stack.pop()), get_variable(stack.pop()), get_variable(stack.pop()), get_variable(stack.pop()), get_variable(stack.pop()), get_variable(stack.pop())

                        self.calls.append(Call(self.nodes[key], state, state_index, op, to, gas))

                elif op == 'SSTORE':
                    stack = copy.deepcopy(state.mstate.stack)

                    index, value = stack.pop(), stack.pop()

                    try:
                        self.sstors[str(index)].append(SStore(self.nodes[key], state, state_index, value))
                    except KeyError:
                        self.sstors[str(index)] = [SStore(self.nodes[key], state, state_index, value)]

                state_index += 1

    def find_storage_write(self, index):

        # Find an SSTOR not constrained by caller that writes to storage index "index"

        try:
            for s in self.sstors[index]:
                taint = True

                for constraint in s.node.constraints:
                    if ("caller" in str(constraint)):
                        taint = False
                        break

                if taint:
                    return s.node.function_name

            return None
        except KeyError:
            return None
