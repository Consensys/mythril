"""
This module implements basic symbolic execution search strategies
"""
from ..state import GlobalState
from typing import List
from random import randrange
from . import BasicSearchStrategy

try:
    from random import choices
except ImportError:

    # This is for supporting python versions < 3.6
    from itertools import accumulate
    from random import random
    from bisect import bisect

    def choices(population, weights=None):
        """
        Returns a random element out of the population based on weight.
        If the relative weights or cumulative weights are not specified,
        the selections are made with equal probability.
        """
        if weights is None:
            return [population[int(random() * len(population))]]
        cum_weights = accumulate(weights)
        return [
            population[
                bisect(cum_weights, random() * cum_weights[-1], 0, len(population) - 1)
            ]
        ]


class DepthFirstSearchStrategy(BasicSearchStrategy):
    """
    Implements a depth first search strategy
    I.E. Follow one path to a leaf, and then continue to the next one
    """

    def get_strategic_global_state(self) -> GlobalState:
        return self.graph.work_list.pop()


class BreadthFirstSearchStrategy(BasicSearchStrategy):
    """
    Implements a breadth first search strategy
    I.E. Execute all states of a "level" before continuing
    """

    def get_strategic_global_state(self) -> GlobalState:
        return self.graph.work_list.pop(0)


class ReturnRandomNaivelyStrategy(BasicSearchStrategy):
    """
    chooses a random state from the worklist with equal likelihood
    """

    def get_strategic_global_state(self) -> GlobalState:
        if len(self.graph.work_list) > 0:
            return self.graph.work_list.pop(randrange(len(self.graph.work_list)))
        else:
            raise IndexError


class ReturnWeightedRandomStrategy(BasicSearchStrategy):
    """
    chooses a random state from the worklist with likelihood based on inverse proportion to depth
    """

    def get_strategic_global_state(self) -> GlobalState:
        probability_distribution = [
            1 / (global_state.mstate.depth + 1) for global_state in self.graph.work_list
        ]
        return self.graph.work_list.pop(
            choices(range(len(self.graph.work_list)), probability_distribution)[0]
        )
