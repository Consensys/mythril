"""
This module implements basic symbolic execution search strategies
"""
from abc import ABC, abstractmethod
from random import randrange

try:
    from random import choices
except ImportError:

    from itertools import accumulate
    from random import random
    from bisect import bisect

    def choices(population, weights=None):
        if weights is None:
            return [population[int(random() * len(population))]]
        cum_weights = accumulate(weights)
        return [population[bisect(cum_weights, random()*cum_weights[-1], 0, len(population)-1)]]


class BasicStrategy(ABC):
    __slots__ = 'work_list', 'max_depth', 'open_states'

    def __init__(self, work_list, max_depth):
        self.work_list = work_list
        self.max_depth = max_depth

    def __iter__(self):
        return self

    @abstractmethod
    def get_strategic_global_state(self):
        raise NotImplementedError("Must be implemented by a subclass")

    def __next__(self):
        try:
            global_state = self.get_strategic_global_state()
            if global_state.mstate.depth >= self.max_depth:
                return self.__next__()
            return global_state
        except IndexError:
            raise StopIteration


class DepthFirstSearchStrategy(BasicStrategy):
    """
    Implements a depth first search strategy
    I.E. Follow one path to a leaf, and then continue to the next one
    """

    def get_strategic_global_state(self):
        return self.work_list.pop()


class BreadthFirstSearchStrategy(BasicStrategy):
    """
    Implements a breadth first search strategy
    I.E. Execute all states of a "level" before continuing
    """

    def get_strategic_global_state(self):
        return self.work_list.pop(0)


class ReturnRandomNaivelyStrategy(BasicStrategy):

    def get_strategic_global_state(self):
        if len(self.work_list) > 0:
            return self.work_list.pop(randrange(len(self.work_list)))
        else:
            raise IndexError


class ReturnWeightedRandomStrategy(BasicStrategy):

    def get_strategic_global_state(self):
        probability_distribution = [global_state.mstate.depth+1 for global_state in self.work_list]
        return self.work_list.pop(choices(range(len(self.work_list)), probability_distribution)[0])

