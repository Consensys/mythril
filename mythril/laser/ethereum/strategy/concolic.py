from mythril.laser.ethereum.state.global_state import GlobalState
from mythril.laser.ethereum.strategy.basic import BasicSearchStrategy
from mythril.laser.ethereum.state.annotation import StateAnnotation
from mythril.laser.ethereum.transaction import ContractCreationTransaction
from mythril.laser.ethereum.util import get_instruction_index
from mythril.analysis.solver import get_transaction_sequence
from mythril.laser.smt import Not
from typing import Dict, cast, List, Any
from copy import copy
from . import CriterionSearchStrategy
import logging


log = logging.getLogger(__name__)


class ConcolicStrategy(CriterionSearchStrategy):
    """
    Executes program concolically using the input trace
    """

    def __init__(
        self,
        work_list: List[GlobalState],
        max_depth: int,
        trace: List[List[int]],
        flip_branch_addr: int,
    ):
        super().__init__(work_list, max_depth)
        self.trace = trace
        self.flip_branch_addr = flip_branch_addr
        self.results: Dict[str, Any] = None

    def get_strategic_global_state(self) -> GlobalState:
        """

        :return:
        """
        while len(self.work_list) > 0:

            state = self.work_list.pop()

            seq_id = len(state.world_state.transaction_sequence) - 1
            concolic_pc = self.trace[seq_id][state.mstate.instr_execution_cnt]

            flip_branch = get_instruction_index(
                state.environment.code.instruction_list, int(self.flip_branch_addr)
            )

            if (
                state.mstate.prev_pc == flip_branch
                and seq_id == len(self.trace) - 1
                and state.mstate.pc == concolic_pc
            ):
                constraint = state.world_state.constraints.pop()
                state.world_state.constraints.append(Not(constraint))

                self.criterion_satisfied = True
                self.results = get_transaction_sequence(
                    state, state.world_state.constraints
                )
            else:
                if state.mstate.pc != concolic_pc:
                    continue

            return state
        raise StopIteration
