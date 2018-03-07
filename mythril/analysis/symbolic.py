from mythril.analysis import solver
from mythril.exceptions import UnsatError
from laser.ethereum import svm
import copy
from .ops import *
import logging


class StateSpace:

    '''
    Symbolic EVM wrapper
    '''
    
    def __init__(self, contracts, dynloader = None, max_depth = 12):

        self.accounts = {}

        for contract in contracts:
            self.accounts[contract.address] = svm.Account(contract.address, contract.get_disassembly(), contract.name)

        self.laser = svm.LaserEVM(self.accounts, dynamic_loader=dynloader, max_depth=max_depth)
        self.laser.sym_exec(contracts[0].address)

        # self.modules = modules
        self.nodes = self.laser.nodes
        self.edges = self.laser.edges

        # Some pre-analysis

        self.calls = []
        self.sstors = {}

        for key in self.nodes:

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
                            self.calls.append(Call(self.nodes[key], instruction['address'], op, to, gas, value, state.mstate.memory[meminstart.val:meminsz.val*4]))
                        else:
                            self.calls.append(Call(self.nodes[key], instruction['address'], op, to, gas, value))                     
                    else:
                        gas, to, meminstart, meminsz, memoutstart, memoutsz = \
                            get_variable(stack.pop()), get_variable(stack.pop()), get_variable(stack.pop()), get_variable(stack.pop()), get_variable(stack.pop()), get_variable(stack.pop())

                        self.calls.append(Call(self.nodes[key], instruction['address'], op, to, gas))

                '''
                elif op == 'SSTORE':
                    stack = copy.deepcopy(state.mstate.stack)

                    index, value = stack.pop(), stack.pop()

                    try:
                        self.sstors[str(index)].append(SStore(self.nodes[key], instruction['address'], value))
                    except KeyError:
                        self.sstors[str(index)] = [SStore(self.nodes[key], instruction['address'], value)]
                '''



    def find_storage_write(self, index):

        # Find a an unconstrained SSTOR that writes to storage index "index"

        try:
            for s in self.sstors[index]:
                taint = True

                for constraint in s.node.constraints:
                    if ("caller" in str(constraint)):
                        taint = False
                        break

                    return s.node.function_name

            return None
        except KeyError:
            return None

