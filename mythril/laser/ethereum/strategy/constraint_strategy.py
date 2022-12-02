from mythril.laser.ethereum.state.global_state import GlobalState
from mythril.laser.ethereum.strategy.basic import BasicSearchStrategy
from mythril.laser.ethereum.state.annotation import StateAnnotation
from mythril.laser.ethereum.transaction import ContractCreationTransaction
from mythril.laser.smt import And, simplify
from mythril.support.support_utils import ModelCache

from typing import Dict, cast, List
from collections import OrderedDict
from copy import copy, deepcopy
from functools import lru_cache
import logging
import z3
from time import time

log = logging.getLogger(__name__)


class DelayConstraintStrategy(BasicSearchStrategy):
    def __init__(self, work_list, max_depth, **kwargs):
        super().__init__(work_list, max_depth)
        self.model_cache = ModelCache()
        self.pending_worklist = []
        log.info("Loaded search strategy extension: DelayConstraintStrategy")

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
                state = self.work_list[0]
                c_val = self.model_cache.check_quick_sat(
                    simplify(And(*state.world_state.constraints)).raw
                )
                if c_val == False:
                    self.pending_worklist.append(state)
                    self.work_list.pop(0)
                else:
                    return self.work_list.pop(0)
