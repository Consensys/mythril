from mythril.analysis.report import Issue
from mythril.solidnotary.transactiontrace import TransactionTrace
from mythril.solidnotary.solidnotary import get_transaction_traces
from mythril.solidnotary.z3utility import  are_satisfiable
import logging


'''
    Build execution traces from the statespace 
'''

def print_obj(obj):
    print()
    print(type(obj))
    print(obj)
    print(dir(obj))
    print(obj.decl())
    print(obj.params())
    print(obj.children())
    print()


def execute(statespace):

    logging.debug("Executing module: Transaction End")

    traces = []

    traces = get_transaction_traces(statespace)
    for trace in traces:
        comp_trace_lvls = trace.apply_up_to_trace_levels(traces, 3)
        for trace_lvl in comp_trace_lvls:
            for t in trace_lvl:
                if t.lvl == 4:
                    t.pp_trace()

#    for trace in traces:
#        trace.pp_trace()

    #print("==== Second level traces ====")
    #for trace in traces:
    #    comp_trace_lvls = trace.apply_up_to_trace_levels(traces, 1)
        #for trace_lvl in range(len(comp_trace_lvls)):
            # print("\nTrace level: " + str(trace_lvl))
            #for comp_trace in comp_trace_lvls[trace_lvl]:
            #    print(comp_trace.storage)
                # for k, s in comp_trace.storage.items():
                #    print_obj(s)

    return []
