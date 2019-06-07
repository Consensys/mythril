from mythril.laser.ethereum.state.global_state import GlobalState
from mythril.laser.ethereum.strategy.basic import BreadthFirstSearchStrategy
from mythril.laser.ethereum.state.annotation import StateAnnotation
from mythril.laser.ethereum import util
from typing import Dict, cast, List
from copy import copy
import logging


JUMPDEST_LIMIT = 4
log = logging.getLogger(__name__)


class JumpdestCountAnnotation(StateAnnotation):
    """State annotation used when a path is chosen based on a predictable variable."""

    def __init__(self) -> None:
        self._jumpdest_count = {}  # type: Dict[int, int]

    def __copy__(self):
        result = JumpdestCountAnnotation()
        result._jumpdest_count = copy(self._jumpdest_count)
        return result


class BFSBoundedLoopsStrategy(BreadthFirstSearchStrategy):
    """Implements a breadth first search strategy that prunes loops.
    JUMPI instructions are skipped after a jump destination has been
    targeted JUMPDEST_LIMIT times.
    """

    def __init__(self, work_list, max_depth) -> None:
        super().__init__(work_list, max_depth)

    def get_strategic_global_state(self) -> GlobalState:
        """
        :return:
        """

        state = self.work_list.pop(0)

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

        if annotation._jumpdest_count[target] > JUMPDEST_LIMIT:
            log.debug("JUMPDEST limit reached, skipping JUMPI")
            return self.work_list.pop(0)

        return state
