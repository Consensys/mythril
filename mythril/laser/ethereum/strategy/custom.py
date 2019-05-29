from mythril.laser.ethereum.state.global_state import GlobalState
from mythril.laser.ethereum.strategy.basic import BreadthFirstSearchStrategy


class BFSBoundedLoopsStrategy(BreadthFirstSearchStrategy):
    """Implements a breadth first search strategy that prunes loops.
    """

    def __init__(self):
        pass

    def get_strategic_global_state(self) -> GlobalState:
        """
        :return:
        """

        state = self.work_list.pop(0)

        return state
