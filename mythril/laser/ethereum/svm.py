"""This module implements the main symbolic execution engine."""
import logging
from collections import defaultdict
from copy import copy
from datetime import datetime, timedelta
from typing import Callable, Dict, DefaultDict, List, Tuple, Optional

from mythril.laser.ethereum.cfg import NodeFlags, Node, Edge, JumpType
from mythril.laser.ethereum.evm_exceptions import StackUnderflowException
from mythril.laser.ethereum.evm_exceptions import VmException
from mythril.laser.ethereum.instructions import Instruction
from mythril.laser.ethereum.iprof import InstructionProfiler
from mythril.laser.ethereum.plugins.signals import PluginSkipWorldState, PluginSkipState
from mythril.laser.ethereum.state.global_state import GlobalState
from mythril.laser.ethereum.state.world_state import WorldState
from mythril.laser.ethereum.strategy.basic import DepthFirstSearchStrategy
from abc import ABCMeta
from mythril.laser.ethereum.time_handler import time_handler
from mythril.laser.ethereum.transaction import (
    ContractCreationTransaction,
    TransactionEndSignal,
    TransactionStartSignal,
    execute_contract_creation,
    execute_message_call,
)
from mythril.laser.smt import symbol_factory

log = logging.getLogger(__name__)


class SVMError(Exception):
    """An exception denoting an unexpected state in symbolic execution."""

    pass


class LaserEVM:
    """The LASER EVM.

    Just as Mithril had to be mined at great efforts to provide the
    Dwarves with their exceptional armour, LASER stands at the heart of
    Mythril, digging deep in the depths of call graphs, unearthing the
    most precious symbolic call data, that is then hand-forged into
    beautiful and strong security issues by the experienced smiths we
    call detection modules. It is truly a magnificent symbiosis.
    """

    def __init__(
        self,
        dynamic_loader=None,
        max_depth=float("inf"),
        execution_timeout=60,
        create_timeout=10,
        strategy=DepthFirstSearchStrategy,
        transaction_count=2,
        requires_statespace=True,
        enable_iprof=False,
        enable_coverage_strategy=False,
        instruction_laser_plugin=None,
    ) -> None:
        """
        Initializes the laser evm object

        :param dynamic_loader: Loads data from chain
        :param max_depth: Maximum execution depth this vm should execute
        :param execution_timeout: Time to take for execution
        :param create_timeout: Time to take for contract creation
        :param strategy: Execution search strategy
        :param transaction_count: The amount of transactions to execute
        :param requires_statespace: Variable indicating whether the statespace should be recorded
        :param enable_iprof: Variable indicating whether instruction profiling should be turned on
        """
        self.open_states = []  # type: List[WorldState]

        self.total_states = 0
        self.dynamic_loader = dynamic_loader

        # TODO: What about using a deque here?
        self.work_list = []  # type: List[GlobalState]
        self.strategy = strategy(self.work_list, max_depth)
        self.max_depth = max_depth
        self.transaction_count = transaction_count

        self.execution_timeout = execution_timeout or 0
        self.create_timeout = create_timeout

        self.requires_statespace = requires_statespace
        if self.requires_statespace:
            self.nodes = {}  # type: Dict[int, Node]
            self.edges = []  # type: List[Edge]

        self.time = None  # type: datetime

        self.pre_hooks = defaultdict(list)  # type: DefaultDict[str, List[Callable]]
        self.post_hooks = defaultdict(list)  # type: DefaultDict[str, List[Callable]]

        self._add_world_state_hooks = []  # type: List[Callable]
        self._execute_state_hooks = []  # type: List[Callable]

        self._start_sym_trans_hooks = []  # type: List[Callable]
        self._stop_sym_trans_hooks = []  # type: List[Callable]

        self._start_sym_exec_hooks = []  # type: List[Callable]
        self._stop_sym_exec_hooks = []  # type: List[Callable]

        self.iprof = InstructionProfiler() if enable_iprof else None

        if enable_coverage_strategy:
            from mythril.laser.ethereum.plugins.implementations.coverage.coverage_strategy import (
                CoverageStrategy,
            )

            self.strategy = CoverageStrategy(self.strategy, instruction_laser_plugin)

        log.info("LASER EVM initialized with dynamic loader: " + str(dynamic_loader))

    def extend_strategy(self, extension: ABCMeta, *args) -> None:
        self.strategy = extension(self.strategy, args)

    def sym_exec(
        self,
        world_state: WorldState = None,
        target_address: int = None,
        creation_code: str = None,
        contract_name: str = None,
    ) -> None:
        """ Starts symbolic execution
        There are two modes of execution.
        Either we analyze a preconfigured configuration, in which case the world_state and target_address variables
        must be supplied.
        Or we execute the creation code of a contract, in which case the creation code and desired name of that
        contract should be provided.

        :param world_state The world state configuration from which to perform analysis
        :param target_address The address of the contract account in the world state which analysis should target
        :param creation_code The creation code to create the target contract in the symbolic environment
        :param contract_name The name that the created account should be associated with
        """
        pre_configuration_mode = target_address is not None
        scratch_mode = creation_code is not None and contract_name is not None
        if pre_configuration_mode == scratch_mode:
            raise ValueError("Symbolic execution started with invalid parameters")

        log.debug("Starting LASER execution")
        for hook in self._start_sym_exec_hooks:
            hook()

        time_handler.start_execution(self.execution_timeout)
        self.time = datetime.now()

        if pre_configuration_mode:
            self.open_states = [world_state]
            log.info("Starting message call transaction to {}".format(target_address))
            self._execute_transactions(symbol_factory.BitVecVal(target_address, 256))

        elif scratch_mode:
            log.info("Starting contract creation transaction")

            created_account = execute_contract_creation(
                self, creation_code, contract_name, world_state=world_state
            )
            log.info(
                "Finished contract creation, found {} open states".format(
                    len(self.open_states)
                )
            )

            if len(self.open_states) == 0:
                log.warning(
                    "No contract was created during the execution of contract creation "
                    "Increase the resources for creation execution (--max-depth or --create-timeout)"
                )

            self._execute_transactions(created_account.address)

        log.info("Finished symbolic execution")
        if self.requires_statespace:
            log.info(
                "%d nodes, %d edges, %d total states",
                len(self.nodes),
                len(self.edges),
                self.total_states,
            )

        if self.iprof is not None:
            log.info("Instruction Statistics:\n{}".format(self.iprof))

        for hook in self._stop_sym_exec_hooks:
            hook()

    def _execute_transactions(self, address):
        """This function executes multiple transactions on the address

        :param address: Address of the contract
        :return:
        """
        self.time = datetime.now()

        for i in range(self.transaction_count):
            log.info(
                "Starting message call transaction, iteration: {}, {} initial states".format(
                    i, len(self.open_states)
                )
            )
            for hook in self._start_sym_trans_hooks:
                hook()

            execute_message_call(self, address)

            for hook in self._stop_sym_trans_hooks:
                hook()

    def exec(self, create=False, track_gas=False) -> Optional[List[GlobalState]]:
        """

        :param create:
        :param track_gas:
        :return:
        """
        final_states = []  # type: List[GlobalState]
        for global_state in self.strategy:
            if (
                self.create_timeout
                and create
                and self.time + timedelta(seconds=self.create_timeout) <= datetime.now()
            ):
                log.debug("Hit create timeout, returning.")
                return final_states + [global_state] if track_gas else None

            if (
                self.execution_timeout
                and self.time + timedelta(seconds=self.execution_timeout)
                <= datetime.now()
                and not create
            ):
                log.debug("Hit execution timeout, returning.")
                return final_states + [global_state] if track_gas else None

            try:
                new_states, op_code = self.execute_state(global_state)
            except NotImplementedError:
                log.debug("Encountered unimplemented instruction")
                continue

            new_states = [
                state for state in new_states if state.mstate.constraints.is_possible
            ]

            self.manage_cfg(op_code, new_states)  # TODO: What about op_code is None?
            if new_states:
                self.work_list += new_states
            elif track_gas:
                final_states.append(global_state)
            self.total_states += len(new_states)

        return final_states if track_gas else None

    def _add_world_state(self, global_state: GlobalState):
        """ Stores the world_state of the passed global state in the open states"""

        for hook in self._add_world_state_hooks:
            try:
                hook(global_state)
            except PluginSkipWorldState:
                return

        self.open_states.append(global_state.world_state)

    def execute_state(
        self, global_state: GlobalState
    ) -> Tuple[List[GlobalState], Optional[str]]:
        """Execute a single instruction in global_state.

        :param global_state:
        :return: A list of successor states.
        """
        # Execute hooks
        for hook in self._execute_state_hooks:
            hook(global_state)

        instructions = global_state.environment.code.instruction_list

        try:
            op_code = instructions[global_state.mstate.pc]["opcode"]
        except IndexError:
            self._add_world_state(global_state)
            return [], None

        try:
            self._execute_pre_hook(op_code, global_state)
        except PluginSkipState:
            self._add_world_state(global_state)
            return [], None

        try:
            new_global_states = Instruction(
                op_code, self.dynamic_loader, self.iprof
            ).evaluate(global_state)

        except VmException as e:
            transaction, return_global_state = global_state.transaction_stack.pop()

            if return_global_state is None:
                # In this case we don't put an unmodified world state in the open_states list Since in the case of an
                #  exceptional halt all changes should be discarded, and this world state would not provide us with a
                #  previously unseen world state
                log.debug("Encountered a VmException, ending path: `{}`".format(str(e)))
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
            new_global_state.mstate.constraints = (
                start_signal.global_state.mstate.constraints
            )

            log.debug("Starting new transaction %s", start_signal.transaction)

            return [new_global_state], op_code

        except TransactionEndSignal as end_signal:
            transaction, return_global_state = end_signal.global_state.transaction_stack[
                -1
            ]

            log.debug("Ending transaction %s.", transaction)

            if return_global_state is None:
                if (
                    not isinstance(transaction, ContractCreationTransaction)
                    or transaction.return_data
                ) and not end_signal.revert:
                    end_signal.global_state.world_state.node = global_state.node
                    self._add_world_state(end_signal.global_state)
                new_global_states = []
            else:
                # First execute the post hook for the transaction ending instruction
                self._execute_post_hook(op_code, [end_signal.global_state])

                new_global_states = self._end_message_call(
                    copy(return_global_state),
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
        """

        :param return_global_state:
        :param global_state:
        :param revert_changes:
        :param return_data:
        :return:
        """

        return_global_state.mstate.constraints += global_state.mstate.constraints
        # Resume execution of the transaction initializing instruction
        op_code = return_global_state.environment.code.instruction_list[
            return_global_state.mstate.pc
        ]["opcode"]

        # Set execution result in the return_state
        return_global_state.last_return_data = return_data
        if not revert_changes:
            return_global_state.world_state = copy(global_state.world_state)
            return_global_state.environment.active_account = global_state.accounts[
                return_global_state.environment.active_account.address.value
            ]

        # Execute the post instruction handler
        new_global_states = Instruction(
            op_code, self.dynamic_loader, self.iprof
        ).evaluate(return_global_state, True)

        # In order to get a nice call graph we need to set the nodes here
        for state in new_global_states:
            state.node = global_state.node

        return new_global_states

    def manage_cfg(self, opcode: str, new_states: List[GlobalState]) -> None:
        """

        :param opcode:
        :param new_states:
        """
        if opcode == "JUMP":
            assert len(new_states) <= 1
            for state in new_states:
                self._new_node_state(state)
        elif opcode == "JUMPI":
            assert len(new_states) <= 2
            for state in new_states:
                self._new_node_state(
                    state, JumpType.CONDITIONAL, state.mstate.constraints[-1]
                )
        elif opcode in ("SLOAD", "SSTORE") and len(new_states) > 1:
            for state in new_states:
                self._new_node_state(
                    state, JumpType.CONDITIONAL, state.mstate.constraints[-1]
                )
        elif opcode == "RETURN":
            for state in new_states:
                self._new_node_state(state, JumpType.RETURN)

        for state in new_states:
            state.node.states.append(state)

    def _new_node_state(
        self, state: GlobalState, edge_type=JumpType.UNCONDITIONAL, condition=None
    ) -> None:
        """

        :param state:
        :param edge_type:
        :param condition:
        """
        new_node = Node(state.environment.active_account.contract_name)
        old_node = state.node
        state.node = new_node
        new_node.constraints = state.mstate.constraints
        if self.requires_statespace:
            self.nodes[new_node.uid] = new_node
            self.edges.append(
                Edge(
                    old_node.uid, new_node.uid, edge_type=edge_type, condition=condition
                )
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
        if isinstance(
            state.world_state.transaction_sequence[-1], ContractCreationTransaction
        ):
            environment.active_function_name = "constructor"
        elif address in disassembly.address_to_function_name:
            # Enter a new function
            environment.active_function_name = disassembly.address_to_function_name[
                address
            ]
            new_node.flags |= NodeFlags.FUNC_ENTRY

            log.debug(
                "- Entering function "
                + environment.active_account.contract_name
                + ":"
                + new_node.function_name
            )
        elif address == 0:
            environment.active_function_name = "fallback"

        new_node.function_name = environment.active_function_name

    def register_hooks(self, hook_type: str, hook_dict: Dict[str, List[Callable]]):
        """

        :param hook_type:
        :param hook_dict:
        """
        if hook_type == "pre":
            entrypoint = self.pre_hooks
        elif hook_type == "post":
            entrypoint = self.post_hooks
        else:
            raise ValueError(
                "Invalid hook type %s. Must be one of {pre, post}", hook_type
            )

        for op_code, funcs in hook_dict.items():
            entrypoint[op_code].extend(funcs)

    def register_laser_hooks(self, hook_type: str, hook: Callable):
        """registers the hook with this Laser VM"""
        if hook_type == "add_world_state":
            self._add_world_state_hooks.append(hook)
        elif hook_type == "execute_state":
            self._execute_state_hooks.append(hook)
        elif hook_type == "start_sym_exec":
            self._start_sym_exec_hooks.append(hook)
        elif hook_type == "stop_sym_exec":
            self._stop_sym_exec_hooks.append(hook)
        elif hook_type == "start_sym_trans":
            self._start_sym_trans_hooks.append(hook)
        elif hook_type == "stop_sym_trans":
            self._stop_sym_trans_hooks.append(hook)
        else:
            raise ValueError(
                "Invalid hook type %s. Must be one of {add_world_state}", hook_type
            )

    def laser_hook(self, hook_type: str) -> Callable:
        """Registers the annotated function with register_laser_hooks

        :param hook_type:
        :return: hook decorator
        """

        def hook_decorator(func: Callable):
            """ Hook decorator generated by laser_hook

            :param func: Decorated function
            """
            self.register_laser_hooks(hook_type, func)
            return func

        return hook_decorator

    def _execute_pre_hook(self, op_code: str, global_state: GlobalState) -> None:
        """

        :param op_code:
        :param global_state:
        :return:
        """
        if op_code not in self.pre_hooks.keys():
            return
        for hook in self.pre_hooks[op_code]:
            hook(global_state)

    def _execute_post_hook(
        self, op_code: str, global_states: List[GlobalState]
    ) -> None:
        """

        :param op_code:
        :param global_states:
        :return:
        """
        if op_code not in self.post_hooks.keys():
            return

        for hook in self.post_hooks[op_code]:
            for global_state in global_states:
                try:
                    hook(global_state)
                except PluginSkipState:
                    global_states.remove(global_state)

    def pre_hook(self, op_code: str) -> Callable:
        """

        :param op_code:
        :return:
        """

        def hook_decorator(func: Callable):
            """

            :param func:
            :return:
            """
            if op_code not in self.pre_hooks.keys():
                self.pre_hooks[op_code] = []
            self.pre_hooks[op_code].append(func)
            return func

        return hook_decorator

    def post_hook(self, op_code: str) -> Callable:
        """

        :param op_code:
        :return:
        """

        def hook_decorator(func: Callable):
            """

            :param func:
            :return:
            """
            if op_code not in self.post_hooks.keys():
                self.post_hooks[op_code] = []
            self.post_hooks[op_code].append(func)
            return func

        return hook_decorator
