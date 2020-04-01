from functools import lru_cache
from z3 import sat, unknown

from mythril.support.support_args import args
from mythril.laser.smt import Optimize
from mythril.laser.ethereum.time_handler import time_handler
from mythril.exceptions import UnsatError
import logging

log = logging.getLogger(__name__)

# LRU cache works great when used in powers of 2


@lru_cache(maxsize=2 ** 23)
def get_model(constraints, minimize=(), maximize=(), enforce_execution_time=True):
    """
    Returns a model based on given constraints as a tuple
    :param constraints: Tuple of constraints
    :param minimize: Tuple of minimization conditions
    :param maximize: Tuple of maximization conditions
    :param enforce_execution_time: Bool variable which enforces --execution-timeout's time
    :return:
    """
    s = Optimize()
    timeout = args.solver_timeout
    if enforce_execution_time:
        timeout = min(timeout, time_handler.time_remaining() - 500)
        if timeout <= 0:
            raise UnsatError
    s.set_timeout(timeout)
    for constraint in constraints:
        if type(constraint) == bool and not constraint:
            raise UnsatError

    constraints = [constraint for constraint in constraints if type(constraint) != bool]

    for constraint in constraints:
        s.add(constraint)
    for e in minimize:
        s.minimize(e)
    for e in maximize:
        s.maximize(e)
    result = s.check()
    if result == sat:
        return s.model()
    elif result == unknown:
        log.debug("Timeout encountered while solving expression using z3")
    raise UnsatError
