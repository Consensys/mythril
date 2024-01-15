from mythril.laser.ethereum.state.annotation import StateAnnotation
from mythril.laser.ethereum.state.global_state import GlobalState
from mythril.laser.ethereum.state.environment import Environment
from mythril.laser.smt import Bool, BaseArray
from typing import List, Tuple

from copy import deepcopy, copy


class SummaryTrackingAnnotation(StateAnnotation):
    """SummaryTrackingAnnotation
    This annotation is used by the symbolic summary plugin to keep track of data related to a summary that
    will be computed during the future exploration of the annotated world state.
    """

    def __init__(
        self,
        entry: GlobalState,
        storage_pairs: List[Tuple[BaseArray, BaseArray]],
        storage_constraints: List[Bool],
        environment_pair: Tuple[Environment, Environment],
        balance_pair: Tuple[BaseArray, BaseArray],
        code: str,
    ):
        self.entry = entry
        self.trace = []
        self.storage_pairs = storage_pairs
        self.storage_constraints = storage_constraints
        self.environment_pair = environment_pair
        self.balance_pair = balance_pair
        self.code = code

    def __copy__(self):

        annotation = SummaryTrackingAnnotation(
            entry=self.entry,
            storage_pairs=deepcopy(self.storage_pairs),
            storage_constraints=deepcopy(self.storage_constraints),
            environment_pair=deepcopy(self.environment_pair),
            balance_pair=deepcopy(self.balance_pair),
            code=self.code,
        )
        annotation.trace = self.trace
        return annotation
