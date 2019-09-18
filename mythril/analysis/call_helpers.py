"""This module provides helper functions for the analysis modules to deal with
call functionality."""
from typing import Union

from mythril.analysis.ops import VarType, Call, get_variable
from mythril.laser.ethereum.state.global_state import GlobalState
from mythril.laser.ethereum.natives import PRECOMPILE_COUNT


def get_call_from_state(state: GlobalState) -> Union[Call, None]:
    """

    :param state:
    :return:
    """
    instruction = state.get_current_instruction()

    op = instruction["opcode"]
    stack = state.mstate.stack

    if op in ("CALL", "CALLCODE"):
        gas, to, value, meminstart, meminsz, memoutstart, memoutsz = (
            get_variable(stack[-1]),
            get_variable(stack[-2]),
            get_variable(stack[-3]),
            get_variable(stack[-4]),
            get_variable(stack[-5]),
            get_variable(stack[-6]),
            get_variable(stack[-7]),
        )

        if to.type == VarType.CONCRETE and 0 < to.val <= PRECOMPILE_COUNT:
            return None

        if meminstart.type == VarType.CONCRETE and meminsz.type == VarType.CONCRETE:
            return Call(
                state.node,
                state,
                None,
                op,
                to,
                gas,
                value,
                state.mstate.memory[meminstart.val : meminsz.val * 4],
            )
        else:
            return Call(state.node, state, None, op, to, gas, value)

    else:
        gas, to, meminstart, meminsz, memoutstart, memoutsz = (
            get_variable(stack[-1]),
            get_variable(stack[-2]),
            get_variable(stack[-3]),
            get_variable(stack[-4]),
            get_variable(stack[-5]),
            get_variable(stack[-6]),
        )

        return Call(state.node, state, None, op, to, gas)
