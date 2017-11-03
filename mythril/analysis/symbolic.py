from laser.ethereum import svm
from .modules import unchecked_suicide, ether_send
import logging


class StateSpace:

    '''
    Symbolic EVM wrapper
    '''
    
    def __init__(self, contracts, main_contract, dynloader = None, simplify=True):

        # Convert ETHContract objects to LASER SVM "modules"

        modules = {}

        for contract in contracts:
            modules[contract.address] = contract.as_dict()

        _svm = svm.SVM(modules, modules[0], dynamic_loader=dynloader, simplify=simplify)

        _svm.sym_exec()

        self.nodes = _svm.nodes
        self.edges = _svm.edges
