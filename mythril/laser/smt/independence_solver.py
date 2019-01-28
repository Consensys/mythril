import z3

from mythril.laser.smt import Model
from typing import List


def _get_expr_variables(expression: z3.ExprRef):
    """
    Get's the variables that make up the current expression
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
        self.variables = variables or []
        self.conditions = conditions or []


class DependenceMap:
    """ DependenceMap object that maintains a set of dependence buckets, used to separate independent smt queries """

    def __init__(self):
        """ Initializes a DependenceMap object """
        self.buckets = []
        self.variable_map = {}

    def add_condition(self, condition: z3.BoolRef):
        """
        Add condition to the dependence map
        :param condition: The condition that is to be added to the dependence map
        """
        variables = _get_expr_variables(condition)
        relevant_buckets = []
        for variable in variables:
            try:
                bucket = self.variable_map[str(variable)]
                relevant_buckets.append(bucket)
            except KeyError:
                continue

        new_bucket = DependenceBucket(variables, [condition])
        self.buckets.append(new_bucket)

        if relevant_buckets:
            # Merge buckets, and rewrite variable map accordingly
            new_bucket = self.merge_buckets(relevant_buckets + [new_bucket])

        for variable in variables:
            self.variable_map[str(variable)] = new_bucket

    def merge_buckets(self, bucket_list: List[DependenceBucket]):
        """ Merges the buckets in bucket list """
        variables = []
        conditions = []
        for bucket in bucket_list:
            self.buckets.remove(bucket)
            variables += bucket.variables
            conditions += bucket.conditions

        new_bucket = DependenceBucket(variables, conditions)
        self.buckets.append(new_bucket)

        return new_bucket


class IndependenceSolver:
    """An SMT solver object."""

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

    def add(self, constraints: list) -> None:
        """Adds the constraints to this solver.

        :param constraints:
        :return:
        """
        constraints = [c.raw for c in constraints]
        self.constraints.extend(constraints)

    def append(self, constraints: list) -> None:
        """Adds the constraints to this solver.

        :param constraints:
        :return:
        """
        constraints = [c.raw for c in constraints]
        self.constraints.extend(constraints)

    def check(self):
        """Returns z3 smt check result.

        :return:
        """
        dependence_map = DependenceMap()
        for constraint in self.constraints:
            dependence_map.add_condition(constraint)

        self.models = []
        for bucket in dependence_map.buckets:
            self.raw.reset()
            self.raw.append(*bucket.conditions)
            check_result = self.raw.check()
            if check_result == z3.unsat:
                return z3.unsat
            elif check_result == z3.unknown:
                return z3.unknown
            else:
                self.models.append(self.raw.model())

        return z3.sat

    def model(self):
        """Returns z3 model for a solution.

        :return:
        """
        return Model(self.models)

    def reset(self) -> None:
        """Reset this solver."""
        self.constraints = []

    def pop(self, num) -> None:
        """Pop num constraints from this solver.

        :param num:
        """
        self.constraints.pop(num)


from mythril.laser.smt import symbol_factory

a = symbol_factory.BitVecSym("a", 256)
c = symbol_factory.BitVecSym("c", 256)
b = c == (a + symbol_factory.BitVecVal(1, 256))

e = symbol_factory.BitVecSym("d", 256) == symbol_factory.BitVecVal(3, 256)

solver = IndependenceSolver()
solver.add([b, e])
result = solver.check()

print("hello")
