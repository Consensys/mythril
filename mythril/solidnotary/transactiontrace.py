from z3 import *

class TransactionTrace:

    def __init__(self, storage):
        self.storage = storage
        # Todo the constraints of a trace are probably also important here and have to be somehow aggregated
        # Todo Identifiy addional trace information such as blocknumber and more

    """
          Either do only deep checing here and use the proper trace or storage_slot reduction in the apply function. Or do
          both here.
      """

    def deep_equals(trace_lvl1, trace_lvl2):
        return set(trace_lvl1) == set(trace_lvl2) # Todo Impelement an ACTUAL deep comparison

    def simplify_storage(self):
        for k,v in self.storage.items():
            # Todo explore the arguments of this storage simplification in z3 to find ways to further simplify and to
            # sort this expressions for equality comparison
            self.storage[k] = simplify(v)

    """
        Applies the new trace tt on a possibly even changed trace self.
    """
    def apply_trace(self, tt):
        if tt is None:
            return self
        subs_map = list(map(lambda x: (BitVec("storage_" + str(x[0]), 256), x[1]), tt.storage.items()))
        print("_________")
        print(subs_map)
        print(self.storage)
        print("+++++++++")
        for k,v in self.storage.items():
            self.storage[k] = substitute(v, subs_map)
        # Todo Add combination of constraints, this might by tricky if we cannot identify which entrancy constraints of
        # self can be omitted (e.g. when related storage locations were overwritten)
        print(self.storage)
        print("=========")
        self.simplify_storage()
        print(self.storage)
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
            if TransactionTrace.deep_equals(trace_lvl_np1, trace_lvl_n): # Fixpoint detected, function needs to ignore lists, dicts and objects.
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
                if TransactionTrace.deep_equals(trace_lvl_np1, trace_lvl_i): # cycle in the traces of trace chains detected: levels
                    # while repeat themselves, function needs to ignore lists, dicts and objects.
                    return traces_up_to
            traces_up_to.append(trace_lvl_np1)
        return traces_up_to


