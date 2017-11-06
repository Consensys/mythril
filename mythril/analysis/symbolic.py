from laser.ethereum import svm
from .ops import *



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
        self.tainted_sstors = {}

        for key in self.svm.nodes:

            for instruction in self.nodes[key].instruction_list:

                op = instruction['opcode']

                if op in ('CALL', 'CALLCODE', 'DELEGATECALL', 'STATICCALL'):
                    stack = copy.deepcopy(self.svm.nodes[key].states[instruction['address']].stack)

                    if op in ('CALL', 'CALLCODE'):
                        gas, to, value, meminstart, meminsz, memoutstart, memoutsz = \
                            get_variable(stack.pop()), get_variable(stack.pop()), get_variable(stack.pop()), get_variable(stack.pop()), get_variable(stack.pop()), get_variable(stack.pop()), get_variable(stack.pop())

                        self.calls.append(Call(self.nodes[key], instruction['address'], op, to, value))
                    else:
                        gas, to, meminstart, meminsz, memoutstart, memoutsz = \
                            get_variable(stack.pop()), get_variable(stack.pop()), get_variable(stack.pop()), get_variable(stack.pop()), get_variable(stack.pop()), get_variable(stack.pop())

                        self.calls.append(Call(self.nodes[key], instruction['address'], op, to))

                elif op == 'SSTORE':
                    stack = copy.deepcopy(self.svm.nodes[key].states[instruction['address']].stack)

                    index, value = stack.pop(), stack.pop()

                    if 'calldata' in str(value) or 'caller' in str(value):

                        constrained_by_caller = False

                        for constraint in self.svm.nodes[key].constraints:
                            if "caller" in str(constraint) and ("storage_" + str(index)) in str(constraint):
                                constrained_by_caller = True
                                break

                        if not constrained_by_caller:

                            try:
                                self.tainted_sstors[str(index)].append(SStore(self.nodes[key], instruction['address'], value))
                            except KeyError:
                                self.tainted_sstors[str(index)] = [SStore(self.nodes[key], instruction['address'], value)]
             
