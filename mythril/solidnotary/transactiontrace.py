class TransactionTrace:

    def __init__(self, storage):
        self.storage = storage
        # Todo Identifiy addional trace information such as blocknumber and more

    """
        Applies the new trace tt on a possibly even changed trace self.
    """
    def apply_trace(self, tt):
        if tt is None:
            return self
        # Todo implement application of a trace on a existing trace.
        return None

    def apply_traces_parallel(self, traces):
        combined_traces = []
        for trace in traces:
            combined_traces.append(self.apply_trace(trace))
        return combined_traces

    def apply_exact_trace_levels(self, traces, depth):
        # Todo maybe some faster trace build not building one level at a time to e.g.
        # Todo reach level 17 but build 2, then 4, then 8 and then 16 then 17
        trace_lvl_n = [self]
        for i in range(depth):
            trace_lvl_np1 = []
            for trace in trace_lvl_n:
                trace_lvl_np1.append(trace.apply_traces_parallel(traces))
            if deep_equals(trace_lvl_np1, trace_lvl_n): # Fixpoint detected, function needs to ignore lists, dicts and objects.
                return trace_lvl_n
            trace_lvl_n = trace_lvl_np1
        return trace_lvl_n

    def apply_up_to_trace_levels(self, traces, depth):
        traces_up_to = [[self]] # elements are trace_levels
        for i in range(depth):
            trace_lvl_np1 = []
            for trace in traces_up_to[-1]:
                trace_lvl_np1.append(trace.apply_traces_parallel(traces))
            for trace_lvl_i in traces_up_to:
                # the following might be faster to check when using a content representing hash
                if deep_equals(trace_lvl_np1, trace_lvl_i): # cycle in the traces of trace chains detected: levels
                    # while repeat themselves, function needs to ignore lists, dicts and objects.
                    return traces_up_to
            traces_up_to.append(trace_lvl_np1)
        return traces_up_to

    """
        Either do only deep checing here and use the proper trace or storage_slot reduction in the apply function. Or do
        both here.
    """
    def deep_equals(trace_lvl1, trace_lvl2):
        pass
