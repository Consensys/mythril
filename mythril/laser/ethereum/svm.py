from z3 import BitVec
import logging
from mythril.laser.ethereum.state import GlobalState, Environment, CalldataType, Account
from mythril.laser.ethereum.instructions import Instruction
from mythril.laser.ethereum.cfg import NodeFlags, Node, Edge, JumpType
from mythril.laser.ethereum.strategy.basic import DepthFirstSearchStrategy
from functools import reduce

TT256 = 2 ** 256
TT256M1 = 2 ** 256 - 1


class SVMError(Exception):
    pass


'''
Main symbolic execution engine.
'''


class LaserEVM:
    """
    Laser EVM class
    """
    def __init__(self, accounts, dynamic_loader=None, max_depth=22):
        self.instructions_covered = []
        self.accounts = accounts

        self.nodes = {}
        self.edges = []

        self.total_states = 0
        self.dynamic_loader = dynamic_loader

        self.work_list = []
        self.strategy = DepthFirstSearchStrategy(self.work_list, max_depth)
        self.max_depth = max_depth

        self.pre_hooks = {}
        self.post_hooks = {}

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

        self.instructions_covered = [False for _ in environment.code.instruction_list]

        initial_node = Node(environment.active_account.contract_name)
        self.nodes[initial_node.uid] = initial_node

        global_state = GlobalState(self.accounts, environment, initial_node)
        initial_node.states.append(global_state)

        # Empty the work_list before starting an execution
        self.work_list.append(global_state)
        self._sym_exec()

        logging.info("Execution complete")
        logging.info("Achieved {0:.3g}% coverage".format(self.coverage))
        logging.info("%d nodes, %d edges, %d total states", len(self.nodes), len(self.edges), self.total_states)

    def _sym_exec(self):
        for global_state in self.strategy:
            try:
                new_states, op_code = self.execute_state(global_state)
            except NotImplementedError:
                logging.debug("Encountered unimplemented instruction")
                continue

            self.manage_cfg(op_code, new_states)

            self.work_list += new_states
            self.total_states += len(new_states)

    def execute_state(self, global_state):
        instructions = global_state.environment.code.instruction_list
        op_code = instructions[global_state.mstate.pc]['opcode']

        # Only count coverage for the main contract
        if len(global_state.call_stack) == 0:
            self.instructions_covered[global_state.mstate.pc] = True

        self._execute_pre_hook(op_code, global_state)
        new_global_states = Instruction(op_code, self.dynamic_loader).evaluate(global_state)
        self._execute_post_hook(op_code, new_global_states)

        return new_global_states, op_code

    def manage_cfg(self, opcode, new_states):
        if opcode == "JUMP":
            assert len(new_states) <= 1
            for state in new_states:
                self._new_node_state(state)
        elif opcode == "JUMPI":
            for state in new_states:
                self._new_node_state(state, JumpType.CONDITIONAL, state.mstate.constraints[-1])
        elif opcode in ("CALL", 'CALLCODE', 'DELEGATECALL', 'STATICCALL'):
            assert len(new_states) <= 1
            for state in new_states:
                self._new_node_state(state, JumpType.CALL)
        elif opcode == "RETURN":
            for state in new_states:
                self._new_node_state(state, JumpType.RETURN)

        for state in new_states:
            state.node.states.append(state)

    def _new_node_state(self, state, edge_type=JumpType.UNCONDITIONAL, condition=None):
        new_node = Node(state.environment.active_account.contract_name)
        old_node = state.node
        state.node = new_node
        new_node.constraints = state.mstate.constraints
        self.nodes[new_node.uid] = new_node
        self.edges.append(Edge(old_node.uid, new_node.uid, edge_type=edge_type, condition=condition))

        if edge_type == JumpType.RETURN:
            new_node.flags |= NodeFlags.CALL_RETURN
        elif edge_type == JumpType.CALL:
            if 'retval' in str(state.mstate.stack[-1]):
                new_node.flags |= NodeFlags.CALL_RETURN
            else:
                new_node.flags |= NodeFlags.FUNC_ENTRY
        address = state.environment.code.instruction_list[state.mstate.pc - 1]['address']
        
        environment = state.environment
        disassembly = environment.code
        if address in state.environment.code.addr_to_func:
            # Enter a new function

            environment.active_function_name = disassembly.addr_to_func[address]
            new_node.flags |= NodeFlags.FUNC_ENTRY

            logging.info("- Entering function " + environment.active_account.contract_name + ":" + new_node.function_name)
        elif address == 0:
            environment.active_function_name = "fallback"

        new_node.function_name = environment.active_function_name

    @property
    def coverage(self):
        return reduce(lambda sum_, val: sum_ + 1 if val else sum_, self.instructions_covered) / float(
            len(self.instructions_covered)) * 100

    def _execute_pre_hook(self, op_code, global_state):
        if op_code not in self.pre_hooks.keys():
            return
        for hook in self.pre_hooks[op_code]:
            hook(global_state)

    def _execute_post_hook(self, op_code, global_states):
        if op_code not in self.post_hooks.keys():
            return

        for hook in self.post_hooks[op_code]:
            for global_state in global_states:
                hook(global_state)

    def hook(self, op_code):
        def hook_decorator(function):
            if op_code not in self.pre_hooks.keys():
                self.pre_hooks[op_code] = []
            self.pre_hooks[op_code].append(function)
            return function
        return hook_decorator

    def post_hook(self, op_code):
        def hook_decorator(function):
            if op_code not in self.post_hooks.keys():
                self.post_hooks[op_code] = []
            self.post_hooks[op_code].append(function)
            return function
        return hook_decorator
