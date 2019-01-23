from z3 import BitVec, AstRef, ExprRef, BitVecVal, BitVecNumRef

a = BitVec('a', 256)
c = BitVec('c', 256)
b = c * (a + 1)

e = BitVec('d', 256)


def get_expr_variables(expression: ExprRef):
    """
    Get's the variables that make up the current expression
    :param expression:
    :return:
    """
    result = []
    if not expression.children() and not isinstance(expression, BitVecNumRef):
        result.append(expression)
    for child in expression.children():
        c_children = get_expr_variables(child)
        result.extend(c_children)
    return result


class DependenceBucket:
    def __init__(self, variables=None, expressions=None):
        self.variables = variables or []
        self.expressions = expressions or []


class DependenceMap:
    def __init__(self):
        self.buckets = []
        self.variable_map = {}

    def add_condition(self, condition):
        variables = get_expr_variables(condition)
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

    def merge_buckets(self, bucket_list):
        variables = []
        expressions = []
        for bucket in bucket_list:
            self.buckets.remove(bucket)
            variables += bucket.variables
            expressions += bucket.expressions

        new_bucket = DependenceBucket(variables, expressions)
        self.buckets.append(new_bucket)

        return new_bucket

dmap = DependenceMap()

dmap.add_condition(a)
dmap.add_condition(b)
dmap.add_condition(e)

print("yeah")
