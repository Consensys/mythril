from z3 import *
from mythril.analysis.ops import *
from mythril.analysis import solver
from mythril.analysis.report import Issue
from mythril.exceptions import UnsatError
import re
import logging


'''
MODULE DESCRIPTION:

'''


def execute(statespace):

    logging.debug("Executing module: ETHER_SEND")

    issues = []

    for call in statespace.calls:

        state = call.state
        address = state.get_current_instruction()['address']

    return issues
