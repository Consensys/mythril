from mythril.laser.ethereum.state.global_state import GlobalState
from mythril.laser.ethereum.strategy.basic import BasicSearchStrategy
from mythril.laser.ethereum.state.annotation import StateAnnotation
from mythril.laser.ethereum import util
from typing import Dict, cast, List
from copy import copy
import logging


log = logging.getLogger(__name__)


class JumpdestCountAnnotation(StateAnnotation):
    """State annotation that counts the number of jumps per destination."""

    def __init__(self) -> None:
        self._jumpdest_count = {}  # type: Dict[int, int]

    def __copy__(self):
        result = JumpdestCountAnnotation()
        result._jumpdest_count = copy(self._jumpdest_count)
        return result


class BoundedLoopsStrategy(BasicSearchStrategy):
    """Adds loop pruning to the search strategy.
    Ignores JUMPI instruction if the destination was targeted >JUMPDEST_LIMIT times.
    """

    def __init__(self, super_strategy: BasicSearchStrategy, *args) -> None:
        """"""

        self.super_strategy = super_strategy
        self.jumpdest_limit = args[0][0]

        log.info(
            "Loaded search strategy extension: Loop bounds (limit = {})".format(
                self.jumpdest_limit
            )
        )

        BasicSearchStrategy.__init__(
            self, super_strategy.work_list, super_strategy.max_depth
        )

    def get_strategic_global_state(self) -> GlobalState:
        """
        :return:
        """

        while 1:

            state = self.super_strategy.get_strategic_global_state()
            opcode = state.get_current_instruction()["opcode"]

            if opcode != "JUMPI":
                return state

            annotations = cast(
                List[JumpdestCountAnnotation],
                list(state.get_annotations(JumpdestCountAnnotation)),
            )

            if len(annotations) == 0:
                annotation = JumpdestCountAnnotation()
                state.annotate(annotation)
            else:
                annotation = annotations[0]

            target = int(util.get_concrete_int(state.mstate.stack[-1]))

            try:
                annotation._jumpdest_count[target] += 1
            except KeyError:
                annotation._jumpdest_count[target] = 1

            if annotation._jumpdest_count[target] > self.jumpdest_limit:
                log.debug("JUMPDEST limit reached, skipping JUMPI")
                continue

            return state
