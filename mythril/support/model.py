from functools import lru_cache
from z3 import sat, unknown, is_true
from pathlib import Path

from mythril.support.support_args import args
from mythril.laser.smt import Optimize, simplify, And
from mythril.laser.ethereum.time_handler import time_handler
from mythril.exceptions import UnsatError, SolverTimeOutException
import logging
from collections import OrderedDict
from time import time

log = logging.getLogger(__name__)

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


class ModelCache:
    def __init__(self):
        self.model_cache = SimpleLRUCache(size=100)

    @lru_cache(maxsize=2**10)
    def check_quick_sat(self, constraints) -> bool:
        i = 0
        return False
        for model in reversed(self.model_cache.lru_cache.keys()):
            i += 1
            if is_true(model.eval(simplify(And(*constraints)).raw)):
                self.model_cache.put(model, self.model_cache.get(model) + 1)
                return model
        return False

model_cache = ModelCache()
tot = 0
a = 0
f = 0
t = 0
@lru_cache(maxsize=2**23)
def get_model(
    constraints,
    minimize=(),
    maximize=(),
    enforce_execution_time=True,
    solver_timeout=None,
):
    """
    Returns a model based on given constraints as a tuple
    :param constraints: Tuple of constraints
    :param minimize: Tuple of minimization conditions
    :param maximize: Tuple of maximization conditions
    :param enforce_execution_time: Bool variable which enforces --execution-timeout's time
    :return:
    """
    s = Optimize()
    timeout = solver_timeout or args.solver_timeout
    if enforce_execution_time:
        timeout = min(timeout, time_handler.time_remaining() - 500)
        if timeout <= 0:
            raise UnsatError
    s.set_timeout(timeout)
    for constraint in constraints:
        if type(constraint) == bool and not constraint:
            raise UnsatError
    if type(constraints) != tuple:
        constraints = constraints.get_all_constraints()
    constraints = [constraint for constraint in constraints if type(constraint) != bool]
    global tot, a,f, t
    b = time()
    if len(maximize) + len(minimize) == 0:
        t += 1
        f += 1
        ret_model = model_cache.check_quick_sat(tuple(constraints))
        tot += time() - b
        if ret_model:
            f -= 1
            return ret_model
    a += 1
    if a%200 ==0:
        print(tot, f, t) 
    for constraint in constraints:
        s.add(constraint)
    for e in minimize:
        s.minimize(e)
    for e in maximize:
        s.maximize(e)
    if args.solver_log:
        Path(args.solver_log).mkdir(parents=True, exist_ok=True)
        constraint_hash_input = tuple(
            list(constraints)
            + list(minimize)
            + list(maximize)
            + [len(constraints), len(minimize), len(maximize)]
        )
        with open(
            args.solver_log + f"/{abs(hash(constraint_hash_input))}.smt2", "w"
        ) as f:
            f.write(s.sexpr())

    result = s.check()
    if result == sat:
        model_cache.model_cache.put(s.model(), 1)
        return s.model()
    elif result == unknown:
        log.debug("Timeout/Error encountered while solving expression using z3")
        raise SolverTimeOutException
    raise UnsatError
