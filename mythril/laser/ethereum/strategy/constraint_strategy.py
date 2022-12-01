from mythril.laser.ethereum.state.global_state import GlobalState
from mythril.laser.ethereum.strategy.basic import BasicSearchStrategy
from mythril.laser.ethereum.state.annotation import StateAnnotation
from mythril.laser.ethereum.transaction import ContractCreationTransaction
from mythril.laser.smt import And, simplify

from typing import Dict, cast, List
from collections import OrderedDict
from copy import copy
from functools import lru_cache
import logging
import z3
from time import time

log = logging.getLogger(__name__)

x=0
class SimpleLRUCache:
    def __init__(self, size):
        self.size = size
        self.lru_cache = OrderedDict()

    def get(self, key):
        try:
            value = self.lru_cache.pop(key)
            self.lru_cache[key] = value
            return value
        except KeyError:
            return -1

    def put(self, key, value):
        try:
            self.lru_cache.pop(key)
        except KeyError:
            if len(self.lru_cache) >= self.size:
                self.lru_cache.popitem(last=False)
        self.lru_cache[key] = value


class DelayConstraintStrategy(BasicSearchStrategy):
    def __init__(self, work_list, max_depth, **kwargs):
        super().__init__(work_list, max_depth)
        self.model_cache = SimpleLRUCache(size=100)
        self.pending_worklist = []
        log.info("Loaded search strategy extension: DelayConstraintStrategy")

    @lru_cache(maxsize=2**10)
    def check_quick_sat(self, constraints) -> bool:
        for model in self.model_cache.lru_cache:
            if z3.is_true(model.eval(simplify(And(*constraints)).raw, model_completion=True)):
                return True
            else:
                continue
        return False

    def run_check(self):
        return False

    def get_strategic_global_state(self) -> GlobalState:
        """Returns the next state

        :return: Global state
        """
        while True:
            if len(self.work_list) == 0:
                state = self.pending_worklist.pop(0)
                model = state.world_state.constraints.get_model()
                if model is not None:
                    self.model_cache.put(model, 1)
                    return state
            else:
                global x
                state = self.work_list[0]
                a = time()
                c_val = self.check_quick_sat(state.world_state.constraints)
                x += time() - a
                if c_val == False:
                    self.pending_worklist.append(state)
                    self.work_list.pop(0)
                else:
                    return self.work_list.pop(0)
