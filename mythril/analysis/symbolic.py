"""This module contains a wrapper around LASER for extended analysis
purposes."""


from mythril.analysis.security import get_detection_module_hooks, get_detection_modules
from mythril.laser.ethereum import svm
from mythril.laser.ethereum.state.account import Account
from mythril.laser.ethereum.state.world_state import WorldState
from mythril.laser.ethereum.strategy.basic import (
    BreadthFirstSearchStrategy,
    DepthFirstSearchStrategy,
    ReturnRandomNaivelyStrategy,
    ReturnWeightedRandomStrategy,
    BasicSearchStrategy,
)

from mythril.laser.ethereum.transaction.symbolic import (
    ATTACKER_ADDRESS,
    CREATOR_ADDRESS,
)


from mythril.laser.ethereum.plugins.plugin_factory import PluginFactory
from mythril.laser.ethereum.plugins.plugin_loader import LaserPluginLoader

from mythril.laser.ethereum.strategy.extensions.bounded_loops import (
    BoundedLoopsStrategy,
)
from mythril.laser.smt import symbol_factory, BitVec
from typing import Union, List, Type
from mythril.solidity.soliditycontract import EVMContract, SolidityContract
from .ops import Call, VarType, get_variable


class SymExecWrapper:
    """Wrapper class for the LASER Symbolic virtual machine.

    Symbolically executes the code and does a bit of pre-analysis for
    convenience.
    """

    def __init__(
        self,
        contract,
        address: Union[int, str, BitVec],
        strategy,
        dynloader=None,
        max_depth=22,
        execution_timeout=None,
        loop_bound=3,
        create_timeout=None,
        transaction_count=2,
        modules=(),
        compulsory_statespace=True,
        enable_iprof=False,
        disable_dependency_pruning=False,
        run_analysis_modules=True,
        enable_coverage_strategy=False,
        custom_modules_directory="",
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
        if isinstance(address, int):
            address = symbol_factory.BitVecVal(address, 256)

        if strategy == "dfs":
            s_strategy = DepthFirstSearchStrategy  # type: Type[BasicSearchStrategy]
        elif strategy == "bfs":
            s_strategy = BreadthFirstSearchStrategy
        elif strategy == "naive-random":
            s_strategy = ReturnRandomNaivelyStrategy
        elif strategy == "weighted-random":
            s_strategy = ReturnWeightedRandomStrategy
        else:
            raise ValueError("Invalid strategy argument supplied")

        creator_account = Account(
            hex(CREATOR_ADDRESS), "", dynamic_loader=dynloader, contract_name=None
        )
        attacker_account = Account(
            hex(ATTACKER_ADDRESS), "", dynamic_loader=dynloader, contract_name=None
        )

        requires_statespace = (
            compulsory_statespace
            or len(get_detection_modules("post", modules, custom_modules_directory)) > 0
        )
        if not contract.creation_code:
            self.accounts = {hex(ATTACKER_ADDRESS): attacker_account}
        else:
            self.accounts = {
                hex(CREATOR_ADDRESS): creator_account,
                hex(ATTACKER_ADDRESS): attacker_account,
            }

        instruction_laser_plugin = PluginFactory.build_instruction_coverage_plugin()

        self.laser = svm.LaserEVM(
            dynamic_loader=dynloader,
            max_depth=max_depth,
            execution_timeout=execution_timeout,
            strategy=s_strategy,
            create_timeout=create_timeout,
            transaction_count=transaction_count,
            requires_statespace=requires_statespace,
            enable_iprof=enable_iprof,
            enable_coverage_strategy=enable_coverage_strategy,
            instruction_laser_plugin=instruction_laser_plugin,
        )

        if loop_bound is not None:
            self.laser.extend_strategy(BoundedLoopsStrategy, loop_bound)

        plugin_loader = LaserPluginLoader(self.laser)
        plugin_loader.load(PluginFactory.build_mutation_pruner_plugin())
        plugin_loader.load(instruction_laser_plugin)

        if not disable_dependency_pruning:
            plugin_loader.load(PluginFactory.build_dependency_pruner_plugin())

        world_state = WorldState()
        for account in self.accounts.values():
            world_state.put_account(account)

        if run_analysis_modules:
            self.laser.register_hooks(
                hook_type="pre",
                hook_dict=get_detection_module_hooks(
                    modules,
                    hook_type="pre",
                    custom_modules_directory=custom_modules_directory,
                ),
            )
            self.laser.register_hooks(
                hook_type="post",
                hook_dict=get_detection_module_hooks(
                    modules,
                    hook_type="post",
                    custom_modules_directory=custom_modules_directory,
                ),
            )

        if isinstance(contract, SolidityContract):
            self.laser.sym_exec(
                creation_code=contract.creation_code,
                contract_name=contract.name,
                world_state=world_state,
            )
        elif isinstance(contract, EVMContract) and contract.creation_code:
            self.laser.sym_exec(
                creation_code=contract.creation_code,
                contract_name=contract.name,
                world_state=world_state,
            )
        else:
            account = Account(
                address,
                contract.disassembly,
                dynamic_loader=dynloader,
                contract_name=contract.name,
                concrete_storage=True
                if (dynloader is not None and dynloader.storage_loading)
                else False,
            )
            world_state.put_account(account)
            self.laser.sym_exec(world_state=world_state, target_address=address.value)

        if not requires_statespace:
            return

        self.nodes = self.laser.nodes
        self.edges = self.laser.edges

        # Parse calls to make them easily accessible

        self.calls = []  # type: List[Call]

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
                                        meminstart.val : meminsz.val + meminstart.val
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

                state_index += 1
