import mythril.laser.ethereum.util as helper
from copy import copy


def instruction(func):
    """ Wrapper that handles copy and original return """
    def wrapper(self, global_state):
        return global_state, func(self, copy(global_state))
    return wrapper


class Instruction:
    """
    Instruction class is used to mutate a state according to the current instruction
    """
    def __init__(self, op_code):
        self.op_code = op_code

    def evaluate(self, global_state):
        """ Performs the mutation for this instruction """
        instruction_mutator = getattr(self, self.op_code.lower())

        if instruction_mutator is None:
            pass

        new_states = instruction_mutator(global_state)

        return global_state, new_states

    @instruction
    def add(self, global_state):
        """ Add opcode"""
        mstate = global_state.mstate
        # TODO: move to decorator
        mstate.pc += 1
        mstate.stack.append((helper.pop_bitvec(mstate) + helper.pop_bitvec(mstate)))
        return [global_state]



