"""This module contains a wrapper around LASER for extended analysis
purposes."""

import copy

from mythril.analysis.security import get_detection_module_hooks, get_detection_modules
from mythril.laser.ethereum import svm
from mythril.laser.ethereum.plugins.plugin_factory import PluginFactory
from mythril.laser.ethereum.plugins.plugin_loader import LaserPluginLoader
from mythril.laser.ethereum.state.account import Account
from mythril.laser.ethereum.state.world_state import WorldState
from mythril.laser.ethereum.strategy.basic import (
    BreadthFirstSearchStrategy,
    DepthFirstSearchStrategy,
    ReturnRandomNaivelyStrategy,
    ReturnWeightedRandomStrategy,
)
from mythril.laser.smt import symbol_factory
from mythril.solidity.soliditycontract import EVMContract, SolidityContract
from .ops import Call, SStore, VarType, get_variable


class SymExecWrapper:
    """Wrapper class for the LASER Symbolic virtual machine.

    Symbolically executes the code and does a bit of pre-analysis for
    convenience.
    """

    def __init__(
        self,
        contract,
        address,
        strategy,
        dynloader=None,
        max_depth=22,
        execution_timeout=None,
        create_timeout=None,
        transaction_count=2,
        modules=(),
        compulsory_statespace=True,
        enable_iprof=False,
    ):
        """

        :param contract:
        :param address:
        :param strategy:
        :param dynloader:
        :param max_depth:
        :param execution_timeout:
        :param create_timeout:
        :param transaction_count:
        :param modules:
        """
        if isinstance(address, str):
            address = symbol_factory.BitVecVal(int(address, 16), 256)

        if strategy == "dfs":
            s_strategy = DepthFirstSearchStrategy
        elif strategy == "bfs":
            s_strategy = BreadthFirstSearchStrategy
        elif strategy == "naive-random":
            s_strategy = ReturnRandomNaivelyStrategy
        elif strategy == "weighted-random":
            s_strategy = ReturnWeightedRandomStrategy
        else:
            raise ValueError("Invalid strategy argument supplied")

        requires_statespace = (
            compulsory_statespace or len(get_detection_modules("post", modules)) > 0
        )

        self.laser = svm.LaserEVM(
            dynamic_loader=dynloader,
            max_depth=max_depth,
            execution_timeout=execution_timeout,
            strategy=s_strategy,
            create_timeout=create_timeout,
            transaction_count=transaction_count,
            requires_statespace=requires_statespace,
            enable_iprof=enable_iprof,
        )

        plugin_loader = LaserPluginLoader(self.laser)
        plugin_loader.load(PluginFactory.build_mutation_pruner_plugin())
        plugin_loader.load(PluginFactory.build_instruction_coverage_plugin())

        self.laser.register_hooks(
            hook_type="pre",
            hook_dict=get_detection_module_hooks(modules, hook_type="pre"),
        )
        self.laser.register_hooks(
            hook_type="post",
            hook_dict=get_detection_module_hooks(modules, hook_type="post"),
        )

        if isinstance(contract, SolidityContract):
            self.laser.sym_exec(
                creation_code=contract.creation_code, contract_name=contract.name
            )
        elif isinstance(contract, EVMContract) and contract.creation_code:
            self.laser.sym_exec(
                creation_code=contract.creation_code, contract_name=contract.name
            )
        else:
            account = Account(
                address,
                contract.disassembly,
                dynamic_loader=dynloader,
                contract_name=contract.name,
                concrete_storage=False,
            )
            world_state = WorldState()
            world_state.put_account(account)
            self.laser.sym_exec(world_state=world_state, target_address=address)

        if not requires_statespace:
            return

        self.nodes = self.laser.nodes
        self.edges = self.laser.edges

        # Generate lists of interesting operations

        self.calls = []
        self.sstors = {}

        for key in self.nodes:

            state_index = 0

            for state in self.nodes[key].states:

                instruction = state.get_current_instruction()

                op = instruction["opcode"]

                if op in ("CALL", "CALLCODE", "DELEGATECALL", "STATICCALL"):

                    stack = state.mstate.stack

                    if op in ("CALL", "CALLCODE"):
                        gas, to, value, meminstart, meminsz, memoutstart, memoutsz = (
                            get_variable(stack[-1]),
                            get_variable(stack[-2]),
                            get_variable(stack[-3]),
                            get_variable(stack[-4]),
                            get_variable(stack[-5]),
                            get_variable(stack[-6]),
                            get_variable(stack[-7]),
                        )

                        if to.type == VarType.CONCRETE and to.val < 5:
                            # ignore prebuilts
                            continue

                        if (
                            meminstart.type == VarType.CONCRETE
                            and meminsz.type == VarType.CONCRETE
                        ):
                            self.calls.append(
                                Call(
                                    self.nodes[key],
                                    state,
                                    state_index,
                                    op,
                                    to,
                                    gas,
                                    value,
                                    state.mstate.memory[
                                        meminstart.val : meminsz.val * 4
                                    ],
                                )
                            )
                        else:
                            self.calls.append(
                                Call(
                                    self.nodes[key],
                                    state,
                                    state_index,
                                    op,
                                    to,
                                    gas,
                                    value,
                                )
                            )
                    else:
                        gas, to, meminstart, meminsz, memoutstart, memoutsz = (
                            get_variable(stack[-1]),
                            get_variable(stack[-2]),
                            get_variable(stack[-3]),
                            get_variable(stack[-4]),
                            get_variable(stack[-5]),
                            get_variable(stack[-6]),
                        )

                        self.calls.append(
                            Call(self.nodes[key], state, state_index, op, to, gas)
                        )

                elif op == "SSTORE":
                    stack = copy.copy(state.mstate.stack)
                    address = state.environment.active_account.address.value

                    index, value = stack.pop(), stack.pop()

                    try:
                        self.sstors[address]
                    except KeyError:
                        self.sstors[address] = {}

                    try:
                        self.sstors[address][str(index)].append(
                            SStore(self.nodes[key], state, state_index, value)
                        )
                    except KeyError:
                        self.sstors[address][str(index)] = [
                            SStore(self.nodes[key], state, state_index, value)
                        ]

                state_index += 1

    def find_storage_write(self, address, index):
        """

        :param address:
        :param index:
        :return:
        """
        # Find an SSTOR not constrained by caller that writes to storage index "index"

        try:
            for s in self.sstors[address][index]:

                taint = True

                for constraint in s.node.constraints:
                    if "caller" in str(constraint):
                        taint = False
                        break

                if taint:
                    return s.node.function_name

            return None
        except KeyError:
            return None
