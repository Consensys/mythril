from mythril.laser.ethereum.state.global_state import GlobalState
from mythril.laser.ethereum.strategy.basic import BasicSearchStrategy
from mythril.laser.ethereum.state.annotation import StateAnnotation
from mythril.laser.ethereum.transaction import ContractCreationTransaction
from typing import Dict, cast, List
from copy import copy
import logging


log = logging.getLogger(__name__)


class JumpdestCountAnnotation(StateAnnotation):
    """State annotation that counts the number of jumps per destination."""

    def __init__(self) -> None:
        self._reached_count = {}  # type: Dict[int, int]

    def __copy__(self):
        result = JumpdestCountAnnotation()
        result._reached_count = copy(self._reached_count)
        return result


class BoundedLoopsStrategy(BasicSearchStrategy):
    """Adds loop pruning to the search strategy.
    Ignores JUMPI instruction if the destination was targeted >JUMPDEST_LIMIT times.
    """

    def __init__(self, super_strategy: BasicSearchStrategy, *args) -> None:
        """"""

        self.super_strategy = super_strategy
        self.bound = args[0][0]

        log.info(
            "Loaded search strategy extension: Loop bounds (limit = {})".format(
                self.bound
            )
        )

        BasicSearchStrategy.__init__(
            self, super_strategy.work_list, super_strategy.max_depth
        )

    def get_strategic_global_state(self) -> GlobalState:
        """ Returns the next state

        :return: Global state
        """

        while True:

            state = self.super_strategy.get_strategic_global_state()

            annotations = cast(
                List[JumpdestCountAnnotation],
                list(state.get_annotations(JumpdestCountAnnotation)),
            )

            if len(annotations) == 0:
                annotation = JumpdestCountAnnotation()
                state.annotate(annotation)
            else:
                annotation = annotations[0]

            address = state.get_current_instruction()["address"]

            if address in annotation._reached_count:
                annotation._reached_count[address] += 1
            else:
                annotation._reached_count[address] = 1

            # The creation transaction gets a higher loop bound to give it a better chance of success.
            # TODO: There's probably a nicer way to do this

            if isinstance(
                state.current_transaction, ContractCreationTransaction
            ) and annotation._reached_count[address] < max(8, self.bound):
                return state

            elif annotation._reached_count[address] > self.bound:
                log.debug("Loop bound reached, skipping state")
                continue

            return state
