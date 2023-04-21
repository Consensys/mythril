from mythril.support.support_utils import ModelCache
from mythril.support.support_args import args
from mythril.laser.smt import Optimize, simplify, And
from mythril.laser.ethereum.time_handler import time_handler
from mythril.exceptions import UnsatError, SolverTimeOutException

import logging
import os
import signal
import sys

from collections import OrderedDict
from copy import deepcopy
from functools import lru_cache
from multiprocessing.pool import ThreadPool
from multiprocessing import TimeoutError
from pathlib import Path
from time import time
from z3 import sat, unknown, is_true

log = logging.getLogger(__name__)


model_cache = ModelCache()


def solver_worker(
    constraints,
    minimize=(),
    maximize=(),
    solver_timeout=None,
):
    """
    Returns a model based on given constraints as a tuple
    :param constraints: Tuple of constraints
    :param minimize: Tuple of minimization conditions
    :param maximize: Tuple of maximization conditions
    :param solver_timeout: The timeout for solver
    :return:
    """
    s = Optimize()
    s.set_timeout(solver_timeout)

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
    return result, s


@lru_cache(maxsize=2**23)
def get_model(
    constraints,
    minimize=(),
    maximize=(),
    solver_timeout=None,
):
    """
    Returns a model based on given constraints as a tuple
    :param constraints: Tuple of constraints
    :param minimize: Tuple of minimization conditions
    :param maximize: Tuple of maximization conditions
    :param solver_timeout: The solver timeout
    :return:
    """

    solver_timeout = solver_timeout or args.solver_timeout
    solver_timeout = min(solver_timeout, time_handler.time_remaining())
    if solver_timeout <= 0:
        raise SolverTimeOutException
    for constraint in constraints:
        if type(constraint) == bool and not constraint:
            raise UnsatError

    if type(constraints) != tuple:
        constraints = constraints.get_all_constraints()
    constraints = [constraint for constraint in constraints if type(constraint) != bool]

    if len(maximize) + len(minimize) == 0:
        ret_model = model_cache.check_quick_sat(simplify(And(*constraints)).raw)
        if ret_model:
            return ret_model

    pool = ThreadPool(1)
    try:
        thread_result = pool.apply_async(
            solver_worker, args=(constraints, minimize, maximize, solver_timeout)
        )
        try:
            result, s = thread_result.get(solver_timeout)
        except TimeoutError:
            result = unknown
        except Exception:
            log.warning("Encountered an exception while solving expression using z3")
            result = unknown
    finally:
        # This is to prevent any segmentation faults from being displayed from z3
        sys.stdout = open(os.devnull, "w")
        sys.stderr = open(os.devnull, "w")
        pool.terminate()
        sys.stdout = sys.__stdout__
        sys.stderr = sys.__stderr__

    if result == sat:
        model_cache.model_cache.put(s.model(), 1)
        return s.model()
    elif result == unknown:
        log.debug("Timeout/Error encountered while solving expression using z3")
        raise SolverTimeOutException
    raise UnsatError
