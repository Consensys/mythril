from mythril.analysis.report import Issue
import logging


'''
    To print content of the statespace after it was build.
'''

def print_obj(obj):
    print()
    print(obj)
    print(type(obj))
    print(dir(obj))
    print()


def execute(statespace):

    logging.debug("Executing module: Transaction End")

    issues = []

    for k in statespace.nodes:
        node = statespace.nodes[k]

        for state in node.states:

            instruction = state.get_current_instruction()

            if(instruction['opcode'] == "STOP"):
                for k,v in state.environment.active_account.storage.items():
                    print_obj(v)
                # print("opc: {}, add: {} {}".format(instruction['opcode'], instruction['address'], instruction['argument'] if 'argument' in instruction else ""))

    return issues
