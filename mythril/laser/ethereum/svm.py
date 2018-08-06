from z3 import BitVec
import logging
from mythril.disassembler.disassembly import Disassembly
from mythril.laser.ethereum.state import GlobalState, Environment, CalldataType, Account, WorldState
from mythril.laser.ethereum.transaction import MessageCallTransaction, TransactionStartSignal, TransactionEndSignal, ContractCreationTransaction
from mythril.laser.ethereum.instructions import Instruction
from mythril.laser.ethereum.cfg import NodeFlags, Node, Edge, JumpType
from mythril.laser.ethereum.strategy.basic import DepthFirstSearchStrategy
from datetime import datetime, timedelta
from functools import reduce
from copy import copy

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

    def __init__(self, accounts, dynamic_loader=None, max_depth=float('inf'), execution_timeout=60,
                 strategy=DepthFirstSearchStrategy):
        self.instructions_covered = []

        world_state = WorldState()
        world_state.accounts = accounts
        # this sets the initial world state
        self.world_state = world_state
        self.open_states = [world_state]

        self.nodes = {}
        self.edges = []

        self.total_states = 0
        self.dynamic_loader = dynamic_loader

        self.work_list = []
        self.strategy = strategy(self.work_list, max_depth)
        self.max_depth = max_depth
        self.execution_timeout = execution_timeout
        self.time = None

        self.pre_hooks = {}
        self.post_hooks = {}

        logging.info("LASER EVM initialized with dynamic loader: " + str(dynamic_loader))

    def sym_exec(self, main_address=None, creation_code=None):
        logging.debug("Starting LASER execution")
        self.time = datetime.now()

        if main_address:
            self.execute_message_call(main_address)
        elif creation_code:
            self.execute_contract_creation(creation_code)
            self.execute_message_call()

        logging.info("%d nodes, %d edges, %d total states", len(self.nodes), len(self.edges), self.total_states)

    def exec(self):
        for global_state in self.strategy:
            if self.execution_timeout:
                if self.time + timedelta(seconds=self.execution_timeout) <= datetime.now():
                    return
            try:
                new_states, op_code = self.execute_state(global_state)
            except NotImplementedError:
                logging.info("Encountered unimplemented instruction")
                continue

            self.manage_cfg(op_code, new_states)

            self.work_list += new_states
            self.total_states += len(new_states)

    def execute_state(self, global_state):
        instructions = global_state.environment.code.instruction_list
        op_code = instructions[global_state.mstate.pc]['opcode']

        # Only count coverage for the main contract
        if len(global_state.transaction_stack) == 0:
            self.instructions_covered[global_state.mstate.pc] = True

        self._execute_pre_hook(op_code, global_state)
        try:
            new_global_states = Instruction(op_code, self.dynamic_loader).evaluate(global_state)

        except TransactionStartSignal as e:
            # Setup new global state
            new_global_state = e.transaction.initial_global_state()

            new_global_state.transaction_stack.append((e.transaction, global_state))
            new_global_state.node = global_state.node
            new_global_state.mstate.constraints = global_state.mstate.constraints

            return [new_global_state], op_code

        except TransactionEndSignal as e:
            transaction, return_global_state = e.global_state.transaction_stack.pop()

            if return_global_state is None:
                self.open_states.append(e.global_state)
                new_global_states = []
            else:
                # First execute the post hook for the transaction ending instruction
                self._execute_post_hook(op_code, [e.global_state])

                # Resume execution of the transaction initializing instruction
                op_code = return_global_state.environment.code.instruction_list[return_global_state.mstate.pc]['opcode']

                # Set execution result in the return_state
                return_global_state.last_return_data = transaction.return_data
                return_global_state.world_state = copy(global_state.world_state)
                return_global_state.environment.active_account =\
                    global_state.accounts[return_global_state.environment.active_account.contract_name]

                # Execute the post instruction handler
                new_global_states = Instruction(op_code, self.dynamic_loader).evaluate(return_global_state, True)

                # In order to get a nice call graph we need to set the nodes here
                for state in new_global_states:
                    state.node = global_state.node

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
                # Keep track of added contracts so the graph can be generated properly
                if state.environment.active_account.contract_name not in self.world_state.accounts.keys():
                    self.world_state.accounts[state.environment.active_account.contract_name] = state.environment.active_account
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
            try:
                if 'retval' in str(state.mstate.stack[-1]):
                    new_node.flags |= NodeFlags.CALL_RETURN
                else:
                    new_node.flags |= NodeFlags.FUNC_ENTRY
            except IndexError:
                new_node.flags |= NodeFlags.FUNC_ENTRY
        address = state.environment.code.instruction_list[state.mstate.pc - 1]['address']
        
        environment = state.environment
        disassembly = environment.code
        if address in state.environment.code.addr_to_func:
            # Enter a new function

            environment.active_function_name = disassembly.addr_to_func[address]
            new_node.flags |= NodeFlags.FUNC_ENTRY

            logging.info(
                "- Entering function " + environment.active_account.contract_name + ":" + new_node.function_name)
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

    def execute_message_call(self, callee_address):
        caller = BitVec("caller", 256)
        gas_price = BitVec("gasprice", 256)
        call_value = BitVec("callvalue", 256)
        origin = BitVec("origin", 256)

        open_states = self.open_states[:]
        del self.open_states[:]

        for open_world_state in open_states:

            transaction = MessageCallTransaction(
                open_world_state,
                open_world_state[callee_address],
                caller,
                [],
                gas_price,
                call_value,
                origin,
                CalldataType.SYMBOLIC,
            )
            global_state = transaction.initial_global_state()
            global_state.transaction_stack.append((transaction, None))

            new_node = Node(global_state.environment.active_account.contract_name)
            self.instructions_covered = [False for _ in global_state.environment.code.instruction_list]

            self.nodes[new_node.uid] = new_node
            if open_world_state.node:
                self.edges.append(Edge(open_world_state.node.uid, new_node.uid, edge_type=JumpType.Transaction,
                                      condition=None))
            global_state.node = new_node
            new_node.states.append(global_state)
            self.work_list.append(global_state)

        self.exec()
        logging.info("Execution complete")
        logging.info("Achieved {0:.3g}% coverage".format(self.coverage))

    def execute_contract_creation(self, contract_initialization_code):
        caller = BitVec("caller", 256)
        gas_price = BitVec("gasprice", 256)
        call_value = BitVec("callvalue", 256)
        origin = BitVec("origin", 256)

        open_states = self.open_states[:]
        del self.open_states[:]

        for open_world_state in open_states:

            transaction = ContractCreationTransaction(
                open_world_state,
                caller,
                Disassembly(contract_initialization_code),
                [],
                gas_price,
                call_value,
                origin,
                CalldataType.SYMBOLIC,
            )

            global_state = transaction.initial_global_state()
            global_state.transaction_stack.append((transaction, None))

            new_node = Node(global_state.environment.active_account.contract_name)
            self.instructions_covered = [False for _ in global_state.environment.code.instruction_list]

            self.nodes[new_node.uid] = new_node
            if open_world_state.node:
                self.edges.append(Edge(open_world_state.node.uid, new_node.uid, edge_type=JumpType.Transaction,
                                       condition=None))
            global_state.node = new_node
            new_node.states.append(global_state)
            self.work_list.append(global_state)

        self.exec()

        logging.info("Execution complete")
        logging.info("Achieved {0:.3g}% coverage".format(self.coverage))
