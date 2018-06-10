import mythril.laser.ethereum.util as helper
import ethereum.opcodes as opcodes
from z3 import BitVecVal
from copy import copy


class StackUnderflowException(Exception):
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

        instruction_mutator = getattr(self, op)

        if instruction_mutator is None:
            # TODO: Exception
            pass

        return instruction_mutator(global_state)

    @instruction
    def add(self, global_state):
        mstate = global_state.mstate
        mstate.stack.append((helper.pop_bitvec(mstate) + helper.pop_bitvec(mstate)))
        return [global_state]

    @instruction
    def push(self, global_state):
        value = BitVecVal(int(global_state.get_current_instruction()['argument'][2:], 16), 256)
        global_state.mstate.stack.append(value)
        return [global_state]

    @instruction
    def dup(self, global_state):
        value = BitVecVal(int(global_state.get_current_instruction()['argument'][2:], 16), 256)
        global_state.mstate.stack.append(value)
        return [global_state]

    @instruction
    def swap(self, global_state):
        depth = int(self.op_code[4:])
        try:
            stack = global_state.mstate.stack
            stack[-depth - 1], stack[-1] = stack[-1], stack[-depth - 1]
        except IndexError:
            raise StackUnderflowException
