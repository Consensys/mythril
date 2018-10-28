import logging
from typing import List, Tuple, Union, Callable
from mythril.laser.ethereum.state import WorldState, GlobalState
from mythril.laser.ethereum.transaction import (
    TransactionStartSignal,
    TransactionEndSignal,
    ContractCreationTransaction,
)
from mythril.laser.ethereum.evm_exceptions import StackUnderflowException
from mythril.laser.ethereum.instructions import Instruction
from mythril.laser.ethereum.cfg import NodeFlags, Node, Edge, JumpType
from mythril.laser.ethereum.state import Account
from mythril.laser.ethereum.strategy.basic import DepthFirstSearchStrategy
from datetime import datetime, timedelta
from copy import copy
from mythril.laser.ethereum.transaction import (
    execute_contract_creation,
    execute_message_call,
)
from functools import reduce
from mythril.laser.ethereum.evm_exceptions import VmException


class SVMError(Exception):
    pass


"""
Main symbolic execution engine.
"""


class LaserEVM:
    """
    Laser EVM class
    """

    def __init__(
        self,
        accounts: List[Account],
        dynamic_loader=None,
        max_depth=float("inf"),
        execution_timeout=60,
        create_timeout=10,
        strategy=DepthFirstSearchStrategy,
        max_transaction_count=3,
    ):
        world_state = WorldState()
        world_state.accounts = accounts
        # this sets the initial world state
        self.world_state = world_state
        self.open_states = [world_state]

        self.nodes = {}
        self.edges = []
        self.coverage = {}

        self.total_states = 0
        self.dynamic_loader = dynamic_loader

        self.work_list = []
        self.strategy = strategy(self.work_list, max_depth)
        self.max_depth = max_depth
        self.max_transaction_count = max_transaction_count

        self.execution_timeout = execution_timeout
        self.create_timeout = create_timeout

        self.time = None

        self.pre_hooks = {}
        self.post_hooks = {}

        logging.info(
            "LASER EVM initialized with dynamic loader: " + str(dynamic_loader)
        )

    @property
    def accounts(self) -> List[Account]:
        return self.world_state.accounts

    def sym_exec(
        self,
        main_address=None,
        creation_code=None,
        contract_name=None,
        max_transactions=3,
    ) -> None:
        logging.debug("Starting LASER execution")
        self.time = datetime.now()

        if main_address:
            logging.info("Starting message call transaction to {}".format(main_address))
            execute_message_call(self, main_address)
        elif creation_code:
            logging.info("Starting contract creation transaction")
            created_account = execute_contract_creation(
                self, creation_code, contract_name
            )
            logging.info(
                "Finished contract creation, found {} open states".format(
                    len(self.open_states)
                )
            )
            if len(self.open_states) == 0:
                logging.warning(
                    "No contract was created during the execution of contract creation "
                    "Increase the resources for creation execution (--max-depth or --create_timeout)"
                )

            # Reset code coverage
            self.coverage = {}
            for i in range(self.max_transaction_count):
                initial_coverage = self._get_covered_instructions()

                self.time = datetime.now()
                logging.info(
                    "Starting message call transaction, iteration: {}".format(i)
                )
                execute_message_call(self, created_account.address)

                end_coverage = self._get_covered_instructions()
                if end_coverage == initial_coverage:
                    break

        logging.info("Finished symbolic execution")
        logging.info(
            "%d nodes, %d edges, %d total states",
            len(self.nodes),
            len(self.edges),
            self.total_states,
        )
        for code, coverage in self.coverage.items():
            cov = (
                reduce(lambda sum_, val: sum_ + 1 if val else sum_, coverage[1])
                / float(coverage[0])
                * 100
            )
            logging.info("Achieved {} coverage for code: {}".format(cov, code))

    def _get_covered_instructions(self) -> int:
        """ Gets the total number of covered instructions for all accounts in the svm"""
        total_covered_instructions = 0
        for _, cv in self.coverage.items():
            total_covered_instructions += reduce(
                lambda sum_, val: sum_ + 1 if val else sum_, cv[1]
            )
        return total_covered_instructions

    def exec(self, create=False) -> None:
        for global_state in self.strategy:
            if self.execution_timeout and not create:
                if (
                    self.time + timedelta(seconds=self.execution_timeout)
                    <= datetime.now()
                ):
                    return
            elif self.create_timeout and create:
                if self.time + timedelta(seconds=self.create_timeout) <= datetime.now():
                    return

            try:
                new_states, op_code = self.execute_state(global_state)
            except NotImplementedError:
                logging.info("Encountered unimplemented instruction")
                continue

            self.manage_cfg(op_code, new_states)

            self.work_list += new_states
            self.total_states += len(new_states)

    def execute_state(
        self, global_state: GlobalState
    ) -> Tuple[List[GlobalState], Union[str, None]]:
        instructions = global_state.environment.code.instruction_list
        try:
            op_code = instructions[global_state.mstate.pc]["opcode"]
        except IndexError:
            self.open_states.append(global_state.world_state)
            return [], None

        self._execute_pre_hook(op_code, global_state)
        try:
            self._measure_coverage(global_state)
            new_global_states = Instruction(op_code, self.dynamic_loader).evaluate(
                global_state
            )

        except VmException as e:
            transaction, return_global_state = global_state.transaction_stack.pop()

            if return_global_state is None:
                # In this case we don't put an unmodified world state in the open_states list Since in the case of an
                #  exceptional halt all changes should be discarded, and this world state would not provide us with a
                #  previously unseen world state
                logging.debug(
                    "Encountered a VmException, ending path: `{}`".format(str(e))
                )
                new_global_states = []
            else:
                # First execute the post hook for the transaction ending instruction
                self._execute_post_hook(op_code, [global_state])
                new_global_states = self._end_message_call(
                    return_global_state,
                    global_state,
                    revert_changes=True,
                    return_data=None,
                )

        except TransactionStartSignal as start_signal:
            # Setup new global state
            new_global_state = start_signal.transaction.initial_global_state()

            new_global_state.transaction_stack = copy(
                global_state.transaction_stack
            ) + [(start_signal.transaction, global_state)]
            new_global_state.node = global_state.node
            new_global_state.mstate.constraints = global_state.mstate.constraints

            return [new_global_state], op_code

        except TransactionEndSignal as end_signal:
            transaction, return_global_state = (
                end_signal.global_state.transaction_stack.pop()
            )

            if return_global_state is None:
                if (
                    not isinstance(transaction, ContractCreationTransaction)
                    or transaction.return_data
                ) and not end_signal.revert:
                    end_signal.global_state.world_state.node = global_state.node
                    self.open_states.append(end_signal.global_state.world_state)
                new_global_states = []
            else:
                # First execute the post hook for the transaction ending instruction
                self._execute_post_hook(op_code, [end_signal.global_state])

                new_global_states = self._end_message_call(
                    return_global_state,
                    global_state,
                    revert_changes=False or end_signal.revert,
                    return_data=transaction.return_data,
                )

        self._execute_post_hook(op_code, new_global_states)

        return new_global_states, op_code

    def _end_message_call(
        self,
        return_global_state: GlobalState,
        global_state: GlobalState,
        revert_changes=False,
        return_data=None,
    ) -> List[GlobalState]:
        # Resume execution of the transaction initializing instruction
        op_code = return_global_state.environment.code.instruction_list[
            return_global_state.mstate.pc
        ]["opcode"]

        # Set execution result in the return_state
        return_global_state.last_return_data = return_data
        if not revert_changes:
            return_global_state.world_state = copy(global_state.world_state)
            return_global_state.environment.active_account = global_state.accounts[
                return_global_state.environment.active_account.address
            ]

        # Execute the post instruction handler
        new_global_states = Instruction(op_code, self.dynamic_loader).evaluate(
            return_global_state, True
        )

        # In order to get a nice call graph we need to set the nodes here
        for state in new_global_states:
            state.node = global_state.node

        return new_global_states

    def _measure_coverage(self, global_state: GlobalState) -> None:
        code = global_state.environment.code.bytecode
        number_of_instructions = len(global_state.environment.code.instruction_list)
        instruction_index = global_state.mstate.pc

        if code not in self.coverage.keys():
            self.coverage[code] = [
                number_of_instructions,
                [False] * number_of_instructions,
            ]

        self.coverage[code][1][instruction_index] = True

    def manage_cfg(self, opcode: str, new_states: List[GlobalState]) -> None:
        if opcode == "JUMP":
            assert len(new_states) <= 1
            for state in new_states:
                self._new_node_state(state)
        elif opcode == "JUMPI":
            for state in new_states:
                self._new_node_state(
                    state, JumpType.CONDITIONAL, state.mstate.constraints[-1]
                )
        elif opcode in ("SLOAD", "SSTORE") and len(new_states) > 1:
            for state in new_states:
                self._new_node_state(
                    state, JumpType.CONDITIONAL, state.mstate.constraints[-1]
                )

        elif opcode in ("CALL", "CALLCODE", "DELEGATECALL", "STATICCALL"):
            assert len(new_states) <= 1
            for state in new_states:
                self._new_node_state(state, JumpType.CALL)
                # Keep track of added contracts so the graph can be generated properly
                if (
                    state.environment.active_account.contract_name
                    not in self.world_state.accounts.keys()
                ):
                    self.world_state.accounts[
                        state.environment.active_account.address
                    ] = state.environment.active_account
        elif opcode == "RETURN":
            for state in new_states:
                self._new_node_state(state, JumpType.RETURN)

        for state in new_states:
            state.node.states.append(state)

    def _new_node_state(
        self, state: GlobalState, edge_type=JumpType.UNCONDITIONAL, condition=None
    ) -> None:
        new_node = Node(state.environment.active_account.contract_name)
        old_node = state.node
        state.node = new_node
        new_node.constraints = state.mstate.constraints
        self.nodes[new_node.uid] = new_node
        self.edges.append(
            Edge(old_node.uid, new_node.uid, edge_type=edge_type, condition=condition)
        )

        if edge_type == JumpType.RETURN:
            new_node.flags |= NodeFlags.CALL_RETURN
        elif edge_type == JumpType.CALL:
            try:
                if "retval" in str(state.mstate.stack[-1]):
                    new_node.flags |= NodeFlags.CALL_RETURN
                else:
                    new_node.flags |= NodeFlags.FUNC_ENTRY
            except StackUnderflowException:
                new_node.flags |= NodeFlags.FUNC_ENTRY
        address = state.environment.code.instruction_list[state.mstate.pc]["address"]

        environment = state.environment
        disassembly = environment.code
        if address in state.environment.code.addr_to_func:
            # Enter a new function

            environment.active_function_name = disassembly.addr_to_func[address]
            new_node.flags |= NodeFlags.FUNC_ENTRY

            logging.debug(
                "- Entering function "
                + environment.active_account.contract_name
                + ":"
                + new_node.function_name
            )
        elif address == 0:
            environment.active_function_name = "fallback"

        new_node.function_name = environment.active_function_name

    def _execute_pre_hook(self, op_code: str, global_state: GlobalState) -> None:
        if op_code not in self.pre_hooks.keys():
            return
        for hook in self.pre_hooks[op_code]:
            hook(global_state)

    def _execute_post_hook(
        self, op_code: str, global_states: List[GlobalState]
    ) -> None:
        if op_code not in self.post_hooks.keys():
            return

        for hook in self.post_hooks[op_code]:
            for global_state in global_states:
                hook(global_state)

    def hook(self, op_code: str) -> Callable:
        def hook_decorator(func: Callable):
            if op_code not in self.pre_hooks.keys():
                self.pre_hooks[op_code] = []
            self.pre_hooks[op_code].append(func)
            return func

        return hook_decorator

    def post_hook(self, op_code: str) -> Callable:
        def hook_decorator(func: Callable):
            if op_code not in self.post_hooks.keys():
                self.post_hooks[op_code] = []
            self.post_hooks[op_code].append(func)
            return func

        return hook_decorator
