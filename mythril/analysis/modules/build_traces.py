from mythril.analysis.report import Issue
from mythril.solidnotary.transactiontrace import TransactionTrace
from mythril.solidnotary.solidnotary import SolidNotary
import logging


'''
    Build execution traces from the statespace 
'''

def print_obj(obj):
    print()
    print(obj)
    # print(dir(obj))
    print()


def execute(statespace):

    logging.debug("Executing module: Transaction End")

    traces = []

    traces = SolidNotary().get_transaction_traces(statespace)

    print("==== Second level traces ====")
    for trace in traces:
        print(trace.apply_traces_parallel(traces))

    return []
