from z3 import BitVec
import logging
from mythril.laser.ethereum.state import GlobalState, Environment, CalldataType, Account
from mythril.laser.ethereum.instructions import Instruction
from mythril.laser.ethereum.cfg import NodeFlags

TT256 = 2 ** 256
TT256M1 = 2 ** 256 - 1


class SVMError(Exception):
    pass


'''
Main symbolic execution engine.
'''

class LaserEVM:
    def __init__(self, accounts, dynamic_loader=None, max_depth=None):
        self.accounts = accounts

        self.nodes = {}
        self.edges = []

        self.total_states = 0
        self.dynamic_loader = dynamic_loader

        self.work_list = []

        logging.info("LASER EVM initialized with dynamic loader: " + str(dynamic_loader))

    def sym_exec(self, main_address):

        logging.debug("Starting LASER execution")

        # Initialize the execution environment
        environment = Environment(
            self.accounts[main_address],
            BitVec("caller", 256),
            [],
            BitVec("gasprice", 256),
            BitVec("callvalue", 256),
            BitVec("origin", 256),
            calldata_type=CalldataType.SYMBOLIC,
        )

        global_state = GlobalState(self.accounts, environment)

        # Empty the work_list before starting an execution
        self.work_list = [global_state]
        self._sym_exec()

        logging.info("Execution complete")
        logging.info("%d nodes, %d edges, %d total states", len(self.nodes), len(self.edges), self.total_states)

    def _sym_exec(self):
        while True:
            try:
                global_state = self.work_list.pop(0)
            except IndexError:
                return

            _, new_states = self.execute_state(global_state)
            self.work_list += new_states
            self.total_states += len(new_states)


    def execute_state(self, global_state):
        instructions = global_state.environment.code.instruction_list
        op_code = instructions[global_state.mstate.pc]['opcode']
        return Instruction(op_code, self.dynamic_loader).evaluate(global_state)

