from laser.ethereum import svm
from .ops import *
import re
import logging


class StateSpace:

    '''
    Symbolic EVM wrapper
    '''
    
    def __init__(self, contracts, dynloader = None, simplified=True):

        # Convert ETHContract objects to LASER SVM "modules"

        modules = {}

        for contract in contracts:
            modules[contract.address] = contract.as_dict()

        self.svm = svm.SVM(modules, simplified=True, dynamic_loader=dynloader)

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

                    logging.info("SSTORE: " + str(index) + " " + str(value))

                    try:
                        self.sstors[str(index)].append(SStore(self.nodes[key], instruction['address'], value))
                    except KeyError:
                        self.sstors[str(index)] = [SStore(self.nodes[key], instruction['address'], value)]

        logging.info(self.sstors)

        self.sstor_analysis()

        for index in self.sstors:
            for s in self.sstors[index]:
                logging.info("SSTOR: " + s.node.function_name + " tainted = " + str(s.tainted))


    def propagate_taint(self, sstor, index):

        if sstor.tainted:
            return

        sstor.tainted = True

        '''
        for index in self.sstors:
            for s in self.sstors[index]:
                for constraint in s.node.constraints:
                    if 'storage_' + index in str(constraint):
                        self.propagate_taint(s, index)
        '''


    def sstor_analysis(self):

        for index in self.sstors:
            for s in self.sstors[index]:

                taint = True

                for constraint in s.node.constraints:
                    # logging.info("LOL " + str(constraint))
                    if (re.search(r'storage_[0-9a-f]+', str(constraint))):
                        taint = False
                        break

                if taint:
                    self.propagate_taint(s, index)
