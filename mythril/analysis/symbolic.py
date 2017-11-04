from laser.ethereum import svm
from .modules import unchecked_suicide, ether_send
import logging


class StateSpace:

    '''
    Symbolic EVM wrapper
    '''
    
    def __init__(self, contracts, dynloader = None, simplified=True):

        # Convert ETHContract objects to LASER SVM "modules"

        modules = {}

        for contract in contracts:
            modules[contract.address] = contract.as_dict()

        _svm = svm.SVM(modules, simplified=True, dynamic_loader=dynloader)

        _svm.sym_exec(contracts[0].address)

        self.modules = modules
        self.nodes = _svm.nodes
        self.edges = _svm.edges

        # Analysis

        self.calls = []
        self.sstores = {}
        self.sloads = {}

        for node in _svm.nodes:
            for instruction in node.instruction_list:
                logging.info(instruction)