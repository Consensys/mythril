from mythril.laser.ethereum.state.global_state import GlobalState
from mythril.laser.ethereum.strategy.basic import BasicSearchStrategy
from mythril.laser.ethereum.state.annotation import StateAnnotation
from mythril.laser.ethereum.transaction import ContractCreationTransaction
from mythril.laser.ethereum.util import get_instruction_index
from mythril.analysis.solver import get_transaction_sequence
from mythril.laser.smt import Not
from mythril.exceptions import UnsatError

from functools import reduce
from typing import Dict, cast, List, Any
from copy import copy
from . import CriterionSearchStrategy
import logging
import operator

log = logging.getLogger(__name__)


class InvalidBranchException(Exception):
    pass


class TraceAnnotation(StateAnnotation):
    """Mutation Annotation

    This is the annotation used by the MutationPruner plugin to record mutations
    """

    def __init__(self, trace=None):
        self.trace = trace or []

    @property
    def persist_over_calls(self) -> bool:
        return True

    def __copy__(self):
        return TraceAnnotation(copy(self.trace))


class ConcolicStrategy(CriterionSearchStrategy):
    """
    Executes program concolically using the input trace till a specific branch
    """

    def __init__(
        self,
        work_list: List[GlobalState],
        max_depth: int,
        trace: List[List[int]],
        flip_branch_addr: int,
    ):
        super().__init__(work_list, max_depth)
        self.trace: List[int] = reduce(operator.iconcat, trace, [])
        self.last_tx_count: int = len(trace)
        self.flip_branch_addr: int = flip_branch_addr
        self.results: Dict[str, Any] = None

    def get_strategic_global_state(self) -> GlobalState:
        """

        :return:
        """
        while len(self.work_list) > 0:

            state = self.work_list.pop()
            seq_id = len(state.world_state.transaction_sequence)
            trace_annotations = cast(
                List[TraceAnnotation],
                list(state.world_state.get_annotations(TraceAnnotation)),
            )

            if len(trace_annotations) == 0:
                annotation = TraceAnnotation()
                state.world_state.annotate(annotation)
            else:
                annotation = trace_annotations[0]
            annotation.trace.append(state.mstate.pc)
            concolic_pc = get_instruction_index(
                state.environment.code.instruction_list, self.flip_branch_addr
            )

            if (
                annotation.trace == self.trace[: len(annotation.trace)]
                and seq_id == self.last_tx_count
                and len(annotation.trace) >= 2
                and annotation.trace[-2] == concolic_pc
            ):
                if state.environment.code.instruction_list[state.mstate.pc] == "JUMPI":
                    log.error(
                        f"The branch {self.flip_branch_addr} does not lead"
                        "to a jump address, skipping this branch"
                    )
                    raise InvalidBranchException
                constraint = state.world_state.constraints.pop()
                state.world_state.constraints.append(Not(constraint))
                self.criterion_satisfied = True
                try:
                    self.results = get_transaction_sequence(
                        state, state.world_state.constraints
                    )
                except UnsatError:
                    self.results = None
            else:
                if annotation.trace != self.trace[: len(annotation.trace)]:
                    continue

            return state
        raise StopIteration
