import z3


class Model:
    """ The model class wraps a z3 model

    This implementation allows for multiple internal models, this is required for the use of an independence solver
    which has models for multiple queries which need an uniform output.
    """

    def __init__(self, models=None):
        """
        Initialize a model object
        :param models: the internal z3 models that this model should use
        """
        self.raw = models or []

    def decls(self):
        """Get the declarations for this model"""
        result = []
        for internal_model in self.raw:
            result.extend(internal_model.decls())
        return result

    def __getitem__(self, item):
        """ Get declaration from model
         If item is an int, then the declaration at offset item is returned
         If item is a declaration, then the interpretation is returned
         """
        for internal_model in self.raw:
            is_last_model = self.raw.index(internal_model) == len(self.raw) - 1

            try:
                result = internal_model[item]
                if result is not None:
                    return result
            except IndexError:
                if is_last_model:
                    raise
                continue
        return None

    def eval(self, expression: z3.ExprRef, model_completion: bool = False):
        """ Evaluate the expression using this model

        :param expression: The expression to evaluate
        :param model_completion: Use the default value if the model has no interpretation of the given expression
        :return: The evaluated expression
        """
        for internal_model in self.raw:
            is_last_model = self.raw.index(internal_model) == len(self.raw) - 1
            is_relevant_model = expression.decl() in list(internal_model.decls())
            if is_relevant_model or is_last_model:
                return internal_model.eval(expression, model_completion)
