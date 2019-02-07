import z3

from mythril.laser.smt.model import Model
from mythril.laser.smt.bool import Bool
from typing import Set, Tuple, Dict, List, cast


def _get_expr_variables(expression: z3.ExprRef) -> List[z3.ExprRef]:
    """
    Gets the variables that make up the current expression
    :param expression:
    :return:
    """
    result = []
    if not expression.children() and not isinstance(expression, z3.BitVecNumRef):
        result.append(expression)
    for child in expression.children():
        c_children = _get_expr_variables(child)
        result.extend(c_children)
    return result


class DependenceBucket:
    """ Bucket object to contain a set of conditions that are dependent on each other """

    def __init__(self, variables=None, conditions=None):
        """
        Initializes a DependenceBucket object
        :param variables: Variables contained in the conditions
        :param conditions: The conditions that are dependent on each other
        """
        self.variables = variables or []  # type: List[z3.ExprRef]
        self.conditions = conditions or []  # type: List[z3.ExprRef]


class DependenceMap:
    """ DependenceMap object that maintains a set of dependence buckets, used to separate independent smt queries """

    def __init__(self):
        """ Initializes a DependenceMap object """
        self.buckets = []  # type: List[DependenceBucket]
        self.variable_map = {}  # type: Dict[str, DependenceBucket]

    def add_condition(self, condition: z3.BoolRef) -> None:
        """
        Add condition to the dependence map
        :param condition: The condition that is to be added to the dependence map
        """
        variables = set(_get_expr_variables(condition))
        relevant_buckets = set()
        for variable in variables:
            try:
                bucket = self.variable_map[str(variable)]
                relevant_buckets.add(bucket)
            except KeyError:
                continue

        new_bucket = DependenceBucket(variables, [condition])
        self.buckets.append(new_bucket)

        if relevant_buckets:
            # Merge buckets, and rewrite variable map accordingly
            relevant_buckets.add(new_bucket)
            new_bucket = self._merge_buckets(relevant_buckets)

        for variable in variables:
            self.variable_map[str(variable)] = new_bucket

    def _merge_buckets(self, bucket_list: Set[DependenceBucket]) -> DependenceBucket:
        """ Merges the buckets in bucket list """
        variables = []  # type: List[str]
        conditions = []  # type: List[z3.BoolRef]
        for bucket in bucket_list:
            self.buckets.remove(bucket)
            variables += bucket.variables
            conditions += bucket.conditions

        new_bucket = DependenceBucket(variables, conditions)
        self.buckets.append(new_bucket)

        return new_bucket


class IndependenceSolver:
    """An SMT solver object that uses independence optimization"""

    def __init__(self):
        """"""
        self.raw = z3.Solver()
        self.constraints = []
        self.models = []

    def set_timeout(self, timeout: int) -> None:
        """Sets the timeout that will be used by this solver, timeout is in
        milliseconds.

        :param timeout:
        """
        self.raw.set(timeout=timeout)

    def add(self, *constraints: Tuple[Bool]) -> None:
        """Adds the constraints to this solver.

        :param constraints: constraints to add
        """
        raw_constraints = [
            c.raw for c in cast(Tuple[Bool], constraints)
        ]  # type: List[z3.BoolRef]
        self.constraints.extend(raw_constraints)

    def append(self, *constraints: Tuple[Bool]) -> None:
        """Adds the constraints to this solver.

        :param constraints: constraints to add
        """
        raw_constraints = [
            c.raw for c in cast(Tuple[Bool], constraints)
        ]  # type: List[z3.BoolRef]
        self.constraints.extend(raw_constraints)

    def check(self) -> z3.CheckSatResult:
        """Returns z3 smt check result. """
        dependence_map = DependenceMap()
        for constraint in self.constraints:
            dependence_map.add_condition(constraint)

        self.models = []
        for bucket in dependence_map.buckets:
            self.raw.reset()
            self.raw.append(*bucket.conditions)
            check_result = self.raw.check()
            if check_result == z3.sat:
                self.models.append(self.raw.model())
            else:
                return check_result

        return z3.sat

    def model(self) -> Model:
        """Returns z3 model for a solution. """
        return Model(self.models)

    def reset(self) -> None:
        """Reset this solver."""
        self.constraints = []

    def pop(self, num) -> None:
        """Pop num constraints from this solver.
        """
        self.constraints.pop(num)
