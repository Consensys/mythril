from mythril.laser.ethereum.state.annotation import StateAnnotation
from mythril.laser.ethereum.svm import LaserEVM


class MutationAnnotation(StateAnnotation):
    """Mutation Annotation

    This is the annotation used by the MutationPruner plugin to record mutations
    """
    pass


class MutationPruner:
    """Mutation pruner plugin

    Let S be a world state from which T is a symbolic transaction, and S' is the resulting world state.
    In a situation where T does not execute any mutating instructions we can safely abandon further analysis on top of
    state S'. This is for the reason that we already performed analysis on S, which is equivalent.

    This optimization inhibits path explosion caused by "clean" behaviour

    The basic operation of this plugin is as follows:
     - Hook all mutating operations and introduce a MutationAnnotation to the global state on execution of the hook
     - Hook the svm EndTransaction on execution filter the states that do not have a mutation annotation

    """
    def __init__(self):
        pass

    def initialize(self, symbolic_vm: LaserEVM):
        pass
