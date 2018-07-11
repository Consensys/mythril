from mythril import ether
from mythril.laser.ethereum import svm
import copy
import logging
from .ops import get_variable, SStore, Call, VarType
from mythril.laser.ethereum.strategy.basic import DepthFirstSearchStrategy, BreadthFirstSearchStrategy


class SymExecWrapper:

    '''
    Wrapper class for the LASER Symbolic virtual machine. Symbolically executes the code and does a bit of pre-analysis for convenience.
    '''

    def __init__(self, contract, address, strategy, dynloader=None, max_depth=None, execution_timeout=None):
        s_strategy = None
        if strategy == 'dfs':
            s_strategy = DepthFirstSearchStrategy
        elif strategy == 'bfs':
            s_strategy = BreadthFirstSearchStrategy
        else:
            raise ValueError("Invalid strategy argument supplied")

        account = svm.Account(address, contract.disassembly, contract_name=contract.name)

        self.accounts = {address: account}

        self.laser = svm.LaserEVM(self.accounts, dynamic_loader=dynloader, max_depth=max_depth, execution_timeout=execution_timeout, strategy=s_strategy)

        self.laser.sym_exec(address)

        self.nodes = self.laser.nodes
        self.edges = self.laser.edges

        # Generate lists of interesting operations

        self.calls = []
        self.sstors = {}

        for key in self.nodes:

            state_index = 0

            for state in self.nodes[key].states:

                instruction = state.get_current_instruction()

                op = instruction['opcode']

                if op in ('CALL', 'CALLCODE', 'DELEGATECALL', 'STATICCALL'):

                    stack = state.mstate.stack

                    if op in ('CALL', 'CALLCODE'):
                        gas, to, value, meminstart, meminsz, memoutstart, memoutsz = \
                            get_variable(stack[-1]), get_variable(stack[-2]), get_variable(stack[-3]), get_variable(stack[-4]), get_variable(stack[-5]), get_variable(stack[-6]), get_variable(stack[-7])

                        if to.type == VarType.CONCRETE and to.val < 5:
                                # ignore prebuilts
                                continue

                        if (meminstart.type == VarType.CONCRETE and meminsz.type == VarType.CONCRETE):
                            self.calls.append(Call(self.nodes[key], state, state_index, op, to, gas, value, state.mstate.memory[meminstart.val:meminsz.val * 4]))
                        else:
                            self.calls.append(Call(self.nodes[key], state, state_index, op, to, gas, value))
                    else:
                        gas, to, meminstart, meminsz, memoutstart, memoutsz = \
                            get_variable(stack[-1]), get_variable(stack[-2]), get_variable(stack[-3]), get_variable(stack[-4]), get_variable(stack[-5]), get_variable(stack[-6])

                        self.calls.append(Call(self.nodes[key], state, state_index, op, to, gas))

                elif op == 'SSTORE':
                    stack = copy.deepcopy(state.mstate.stack)
                    address = state.environment.active_account.address

                    index, value = stack.pop(), stack.pop()

                    try:
                        self.sstors[address]
                    except KeyError:
                        self.sstors[address] = {}

                    try:
                        self.sstors[address][str(index)].append(SStore(self.nodes[key], state, state_index, value))
                    except KeyError:
                        self.sstors[address][str(index)] = [SStore(self.nodes[key], state, state_index, value)]

                state_index += 1

    def find_storage_write(self, address, index):

        # Find an SSTOR not constrained by caller that writes to storage index "index"

        try:
            for s in self.sstors[address][index]:

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
