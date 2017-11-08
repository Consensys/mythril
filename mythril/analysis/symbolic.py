from laser.ethereum import svm
from .ops import *
import re
import logging


class StateSpace:

    '''
    Symbolic EVM wrapper
    '''
    
    def __init__(self, contracts, dynloader = None, simplified=False):

        # Convert ETHContract objects to LASER SVM "modules"

        modules = {}

        for contract in contracts:
            modules[contract.address] = contract.as_dict()

        self.svm = svm.SVM(modules, simplified = simplified, dynamic_loader=dynloader)

        self.svm.sym_exec(contracts[0].address)

        self.modules = modules
        self.nodes = self.svm.nodes
        self.edges = self.svm.edges

        # Analysis

        self.calls = []
        self.suicides = []
        self.sstors = {}

        for key in self.svm.nodes:

            for instruction in self.nodes[key].instruction_list:

                op = instruction['opcode']

                if op in ('CALL', 'CALLCODE', 'DELEGATECALL', 'STATICCALL'):
                    stack = copy.deepcopy(self.svm.nodes[key].states[instruction['address']].stack)

                    if op in ('CALL', 'CALLCODE'):
                        gas, to, value, meminstart, meminsz, memoutstart, memoutsz = \
                            get_variable(stack.pop()), get_variable(stack.pop()), get_variable(stack.pop()), get_variable(stack.pop()), get_variable(stack.pop()), get_variable(stack.pop()), get_variable(stack.pop())

                        self.calls.append(Call(self.nodes[key], instruction['address'], op, to, gas, value))
                    else:
                        gas, to, meminstart, meminsz, memoutstart, memoutsz = \
                            get_variable(stack.pop()), get_variable(stack.pop()), get_variable(stack.pop()), get_variable(stack.pop()), get_variable(stack.pop()), get_variable(stack.pop())

                        self.calls.append(Call(self.nodes[key], instruction['address'], op, to, gas))

                elif op == 'SSTORE':
                    stack = copy.deepcopy(self.svm.nodes[key].states[instruction['address']].stack)

                    index, value = stack.pop(), stack.pop()

                    try:
                        self.sstors[str(index)].append(SStore(self.nodes[key], instruction['address'], value))
                    except KeyError:
                        self.sstors[str(index)] = [SStore(self.nodes[key], instruction['address'], value)]

        self.sstor_analysis()


    def sstor_analysis(self):

        for index in self.sstors:
            for s in self.sstors[index]:

                taint = True

                # For now we simply 'taint' every storage location that can be written to without any constraint on msg.sender

                for constraint in s.node.constraints:
                    if ("caller" in str(constraint)):
                        taint = False
                        break

                if taint:
                    s.tainted = True


    def find_storage_write(self, index):

        # Find a tainted (unconstrained) SSTOR that writes to 'index'

        try:
            for s in self.sstors[index]:
                if s.tainted:
                    return s.node.function_name
            return None
        except KeyError:
            return None

