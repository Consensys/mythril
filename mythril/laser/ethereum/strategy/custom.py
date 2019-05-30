from mythril.laser.ethereum.state.global_state import GlobalState
from mythril.laser.ethereum.strategy.basic import BreadthFirstSearchStrategy
from mythril.laser.ethereum import util
from typing import Dict
import logging


JUMPDEST_LIMIT = 4
log = logging.getLogger(__name__)


class BFSBoundedLoopsStrategy(BreadthFirstSearchStrategy):
    """Implements a breadth first search strategy that prunes loops.
    JUMPI instructions are skipped after a jump destination has been
    targeted JUMPDEST_LIMIT times.
    """

    def __init__(self, work_list, max_depth) -> None:
        super().__init__(work_list, max_depth)
        self._jumpdest_count = {}  # type: Dict[object, dict]

    def get_strategic_global_state(self) -> GlobalState:
        """
        :return:
        """

        state = self.work_list.pop(0)

        opcode = state.get_current_instruction()["opcode"]

        if opcode == "JUMPI":

            transaction = state.current_transaction
            target = util.get_concrete_int(state.mstate.stack[-1])

            if transaction in self._jumpdest_count:

                try:
                    if self._jumpdest_count[transaction][target] == JUMPDEST_LIMIT:
                        log.info("Skipping JUMPI")
                        return self.work_list.pop(0)
                except KeyError:
                    self._jumpdest_count[transaction][target] = 0

                self._jumpdest_count[transaction][target] += 1

            else:
                self._jumpdest_count[transaction] = {}
                self._jumpdest_count[transaction][target] = 0

            log.info(
                "JUMPDEST COUNT: {}".format(self._jumpdest_count[transaction][target])
            )

        return state
