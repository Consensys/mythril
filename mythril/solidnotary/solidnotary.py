import logging
from mythril.solidnotary.transactiontrace import TransactionTrace

class SolidNotary:

    def __init__(self):
        # Todo Parse Annotations and store them in an additional structure
        # Todo receive a list of files or a file, these are modified for the analysis
        pass

    def notarize(self):
        # Todo Instantiate an instance of Mythril, analyze and print the result
        # Todo Find how they are storing results
        pass

    def get_transaction_traces(self, statespace):
        logging.debug("Executing module: Transaction End")

        traces = []

        for k in statespace.nodes:
            node = statespace.nodes[k]
            for state in node.states:
                instruction = state.get_current_instruction()
                if instruction['opcode'] == "STOP":
                    traces.append(TransactionTrace(state.environment.active_account.storage))
        return traces
