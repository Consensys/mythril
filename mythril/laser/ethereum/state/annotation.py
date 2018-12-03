class StateAnnotation:
    """
    The StateAnnotation class is used to persist information over traces. This allows modules to reason about traces
    without the need to traverse the state space themselves.
    """

    @property
    def persist_to_world_state(self) -> bool:
        """
        If this function returns true then laser will also annotate the world state.

        If you want annotations to persist through different user initiated message call transactions
        then this should be enabled.

        The default is set to False
        """
        return False


class NoCopyAnnotation(StateAnnotation):
    """
    This class provides a base annotation class for annotations that shouldn't be copied on every new state.
    Rather the same object should be propagated.
    This is very useful if you are looking to analyze a property over multiple substates
    """

    def __copy__(self):
        return self

    def __deepcopy__(self, _):
        return self
