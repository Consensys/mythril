from mythril.laser.ethereum.state.global_state import GlobalState
from mythril.laser.ethereum.state.constraints import Constraints
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
        flip_branch_addresses: int,
    ):
        super().__init__(work_list, max_depth)
        self.trace: List[int] = reduce(operator.iconcat, trace, [])
        self.last_tx_count: int = len(trace)
        self.flip_branch_addresses: List[str] = flip_branch_addresses
        self.results: Dict[str, Dict[str, Any]] = {}

    def get_strategic_global_state(self) -> GlobalState:
        """
        This function does the following:-
        1) Choose the states by following the concolic trace.
        2) In case we have an executed JUMPI that is in flip_branch_addresses, flip that branch.
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

            # Appends trace
            annotation.trace.append(state.mstate.pc)

            # If trace is 1 then it is not a JUMPI
            if len(annotation.trace) < 2:
                # If trace does not follow the specified path, ignore the state
                if annotation.trace != self.trace[: len(annotation.trace)]:
                    continue
                return state

            # Get the address of the previous pc
            addr: str = str(
                state.environment.code.instruction_list[annotation.trace[-2]]["address"]
            )
            if (
                annotation.trace == self.trace[: len(annotation.trace)]
                and seq_id == self.last_tx_count
                and addr in self.flip_branch_addresses
                and addr not in self.results
            ):
                if (
                    state.environment.code.instruction_list[annotation.trace[-2]][
                        "opcode"
                    ]
                    != "JUMPI"
                ):
                    log.error(
                        f"The branch {addr} does not lead "
                        "to a jump address, skipping this branch"
                    )
                    continue

                constraints = Constraints(state.world_state.constraints[:-1])
                constraints.append(Not(state.world_state.constraints[-1]))

                try:
                    self.results[addr] = get_transaction_sequence(state, constraints)
                except UnsatError:
                    self.results[addr] = None
            elif annotation.trace != self.trace[: len(annotation.trace)]:
                continue

            return state
        raise StopIteration
