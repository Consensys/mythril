from copy import copy
from functools import wraps
import mythril.laser.ethereum.helper as helper


def instruction(func):
    """ Wrapper that handles copy and original return """
    def wrapper(self, global_state):
        return global_state, func(self, copy(global_state))
    return wrapper


class Instruction:
    def __init__(self, opcode):
        self.opcode = opcode

    def evaluate(self, global_state):
        instruction_mutator = getattr(self, self.opcode.lower())

        if instruction_mutator is None:
            pass

        new_states = instruction_mutator(global_state)

        return global_state, new_states

    @instruction
    def add(self, global_state):
        mstate = global_state.mstate
        mstate.stack.append((helper.pop_bitvec(mstate) + helper.pop_bitvec(mstate)))
        return [global_state]



