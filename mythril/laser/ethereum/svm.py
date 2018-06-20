from z3 import BitVec
import logging
from mythril.laser.ethereum.state import GlobalState, Environment, CalldataType, Account
from mythril.laser.ethereum.instructions import Instruction
from mythril.laser.ethereum.cfg import NodeFlags, Node, Edge, JumpType

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

        # TODO: contact name fix
        initial_node = Node(environment.active_account.contract_name)
        self.nodes[initial_node.uid] = initial_node

        global_state = GlobalState(self.accounts, environment, initial_node)
        initial_node.states.append(global_state)

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

            new_states, op_code = self.execute_state(global_state)
            self.manage_cfg(op_code, new_states)

            self.work_list += new_states
            self.total_states += len(new_states)

    def execute_state(self, global_state):
        instructions = global_state.environment.code.instruction_list
        op_code = instructions[global_state.mstate.pc]['opcode']
        return Instruction(op_code, self.dynamic_loader).evaluate(global_state), op_code

    def manage_cfg(self, opcode, new_states):
        if opcode == "JUMP":
            assert len(new_states) == 1
            self._new_node_state(new_states[0])
        elif opcode == "JUMPI":
            for state in new_states:
                self._new_node_state(state, JumpType.CONDITIONAL, state.mstate.constraints[-1])
        elif opcode in ("CALL", 'CALLCODE', 'DELEGATECALL', 'STATICCALL'):
            assert len(new_states) == 1
            self._new_node_state(new_states[0], JumpType.CALL)
        elif opcode == "RETURN":
            for state in new_states:
                self._new_node_state(state, JumpType.RETURN)

        for state in new_states:
            state.node.states.append(state)

    def _new_node_state(self, state, edge_type=JumpType.UNCONDITIONAL, condition=None):
        new_node = Node(state.environment.active_account.contract_name)
        old_node = state.node
        state.node = new_node
        self.nodes[new_node.uid] = new_node
        self.edges.append(Edge(old_node.uid, new_node.uid, edge_type=edge_type, condition=condition))
