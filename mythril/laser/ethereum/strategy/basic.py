class DepthFirstSearchStrategy:

    def __init__(self, content, max_depth):
        self.content = content
        self.max_depth = max_depth

    def __iter__(self):
        return self

    def __next__(self):
        try:
            global_state = self.content.pop(0)
            if global_state.mstate.depth >= self.max_depth:
                return self.__next__()
            return global_state
        except IndexError:
            raise StopIteration()
