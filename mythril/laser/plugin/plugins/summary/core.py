from .summary import SymbolicSummary, substitute_exprs
from .annotations import SummaryTrackingAnnotation
from mythril.analysis.issue_annotation import IssueAnnotation
from mythril.analysis.potential_issues import check_potential_issues
from mythril.analysis import solver
from mythril.analysis.solver import get_transaction_sequence
from mythril.exceptions import UnsatError

from mythril.laser.ethereum.svm import LaserEVM
from mythril.laser.plugin.builder import PluginBuilder
from mythril.laser.plugin.interface import LaserPlugin
from mythril.laser.plugin.signals import PluginSkipState
from mythril.laser.plugin.plugins.plugin_annotations import MutationAnnotation
from mythril.laser.ethereum.transaction.transaction_models import (
    ContractCreationTransaction,
    BaseTransaction,
)
from mythril.support.support_utils import get_code_hash
from mythril.laser.ethereum.function_managers import (
    keccak_function_manager,
    KeccakFunctionManager,
)

from mythril.laser.ethereum.state.global_state import GlobalState
from mythril.laser.ethereum.state.constraints import Constraints
from mythril.laser.ethereum.state.environment import Environment
from mythril.laser.ethereum.state.calldata import SymbolicCalldata
from mythril.laser.ethereum.state.account import Account
from mythril.laser.smt import (
    K,
    Array,
    BaseArray,
    Bool,
    simplify,
    Solver,
    Not,
    Or,
    symbol_factory,
    Expression,
)
from mythril.support.support_args import args
import z3
from typing import Dict, Tuple, List, Optional, Set
from copy import copy, deepcopy
from mythril.support.model import get_model

import logging

log = logging.getLogger(__name__)


class SymbolicSummaryPluginBuilder(PluginBuilder):
    name = "Symbolic Summaries"

    def __call__(self, *args, **kwargs):
        return SymbolicSummaryPlugin()


class SymbolicSummaryPlugin(LaserPlugin):
    def __init__(self):
        self.summaries = []
        args.use_issue_annotations = True
        self.issue_cache: Set[Tuple[str, str, int]] = set()
        self.init_save_states = []
        self.save_init_balance = None

    def initialize(self, symbolic_vm: LaserEVM):
        """Initializes the symbolic summary generating plugin

        Introduces hooks for each instruction
        :param symbolic_vm: the symbolic virtual machine to initialize this plugin for
        """

        """
        @symbolic_vm.laser_hook("start_execute_transactions"):
        def start_exec_txs_hook():
            log.info(f"Started executing transactions")

            symbolic_vm.executed_transactions = True
        """

        @symbolic_vm.laser_hook("stop_sym_exec")
        def stop_sym_exec_hook():
            # Print results
            log.info(f"Generated {len(self.summaries)} summaries")

        @symbolic_vm.laser_hook("execute_state")
        def execute_start_sym_trans_hook(global_state: GlobalState):
            if global_state.mstate.pc == 0:
                if len(global_state.world_state.transaction_sequence) == 2:
                    self.init_save_states.append(deepcopy(global_state))
                self._apply_summaries(laser_evm=symbolic_vm, global_state=global_state)
                self.save_init_balance = deepcopy(global_state.world_state.balances)
                self._summary_entry(global_state)

        @symbolic_vm.post_hook("JUMPI")
        @symbolic_vm.post_hook("JUMP")
        def call_mutator_hook(global_state: GlobalState):
            for annotation in global_state.get_annotations(SummaryTrackingAnnotation):
                annotation.trace.append(global_state.instruction["address"])

        @symbolic_vm.laser_hook("transaction_end")
        def transaction_end_hook(
            global_state: GlobalState,
            transaction: BaseTransaction,
            return_global_state: Optional[GlobalState],
            revert: bool = True,
        ):
            if return_global_state is not None:
                return
            if (
                not isinstance(transaction, ContractCreationTransaction)
                or transaction.return_data
            ) and (not revert or list(global_state.get_annotations(IssueAnnotation))):
                check_potential_issues(global_state)
                self._summary_exit(global_state, transaction, revert)

    def _summary_entry(self, global_state: GlobalState):
        """Handles logic for when the analysis reaches an entry point of a to-be recorded symbolic summary

        :param global_state: The state at the entry of the symbolic summary
        """
        summary_constraints = []
        storage_pairs = []
        # Rewrite storage
        for index, account in global_state.world_state.accounts.items():
            actual_storage = deepcopy(account.storage._standard_storage)
            symbolic_storage = Array(f"{index}_symbolic_storage", 256, 256)
            account.storage._standard_storage = symbolic_storage
            storage_pairs.append((actual_storage, symbolic_storage))
            account.storage.keys_get = set()
            account.storage.keys_set = set()

        # Rewrite balances
        previous_balances, summary_balances = (
            global_state.world_state.balances,
            Array("summary_balance", 256, 256),
        )
        global_state.world_state.balances = summary_balances
        balances_pair = (previous_balances, summary_balances)

        # Rewrite environment
        previous_environment = global_state.environment
        summary_environment = self._create_summary_environment(previous_environment)
        environment_pair = (previous_environment, summary_environment)

        # Construct the summary tracking annotation
        summary_annotation = SummaryTrackingAnnotation(
            global_state,
            storage_pairs,
            summary_constraints,
            environment_pair,
            balances_pair,
            global_state.environment.code.bytecode,
        )

        # Introduce annotation and constraints to the global state
        for constraint in summary_constraints:
            global_state.world_state.constraints.append(constraint)
        global_state.annotate(summary_annotation)

    def _create_summary_environment(self, base_environment: Environment) -> Environment:
        return Environment(
            # No need to rewrite, accounts are handled in other procedure
            active_account=base_environment.active_account,
            # Need to rewrite, different symbol for each transaction
            sender=symbol_factory.BitVecSym("summary_sender", 256),
            # Need to rewrite, different symbol for each transaction
            origin=symbol_factory.BitVecSym("summary_origin", 256),
            # Need to rewrite, different symbol for each transaction
            calldata=SymbolicCalldata("summary"),
            # Need to rewrite, different symbol for each transaction
            gasprice=symbol_factory.BitVecSym("summary_origin", 256),
            # Need to rewrite, different symbol for each transaction
            callvalue=symbol_factory.BitVecSym("summary_callvalue", 256),
            # No need to rewrite, this can be inherited from the original environment
            static=base_environment.static,
            # No need to rewrite, this can be inherited from the original environment
            code=base_environment.code,
            basefee=base_environment.basefee,
        )

    @classmethod
    def _restore_environment(
        cls,
        summary_tracking_annotation: SummaryTrackingAnnotation,
        global_state: GlobalState,
    ):
        global_state.environment = summary_tracking_annotation.environment_pair[0]
        original, summary = summary_tracking_annotation.environment_pair
        # Rewrite sender
        cls._rewrite(global_state, summary.sender, original.sender)
        # Rewrite origin
        cls._rewrite(global_state, summary.origin, original.origin)
        # Rewrite calldata
        cls._rewrite(
            global_state, summary.calldata.calldatasize, original.calldata.calldatasize
        )
        cls._rewrite(
            global_state, summary.calldata._calldata, original.calldata._calldata
        )
        # Rewrite gasprice
        cls._rewrite(global_state, summary.gasprice, original.gasprice)
        # Rewrite callvalue
        cls._rewrite(global_state, summary.callvalue, original.callvalue)

    def check_for_issues(self, global_state):
        for summary in self.summaries:
            for issue in summary.issues:
                self._check_issue(global_state, issue)

    def storage_dependent(self, summary, global_state: GlobalState) -> bool:
        """
        Checks if storage of summary depends on global state's previous storage stores
        """
        total_key_set = set()
        for index in global_state.accounts:
            total_key_set = total_key_set.union(
                global_state.accounts[index].storage.keys_set
            )
        if len(global_state.world_state.transaction_sequence) <= 3:
            return True
        for index, storage_get in summary.get_map.items():
            for key in storage_get:
                if key.symbolic is False:
                    if key in global_state.accounts[index].storage.keys_set:
                        return True
                else:
                    for state_key in global_state.accounts[index].storage.keys_set:
                        s = Solver()
                        s.set_timeout(3000)
                        s.add(state_key == key)
                        s.add(keccak_function_manager.create_conditions())
                        sat = s.check() == z3.sat
                        if sat:
                            return True

        return False

    def _apply_summaries(self, laser_evm: LaserEVM, global_state: GlobalState):
        """
        Applies summaries on the EVM
        """

        pc = global_state.instruction["address"]
        self.check_for_issues(global_state)
        summaries = [
            summary
            for summary in self.summaries
            if summary.entry == pc
            and summary.code == global_state.environment.code.bytecode
            and not summary.revert
            and summary.storage_effect
        ]

        for summary in summaries:
            resulting_state = summary.apply_summary(global_state)
            if resulting_state:
                laser_evm._add_world_state(resulting_state[0])

        if summaries:
            raise PluginSkipState

    def issue_in_cache(
        self, global_state: GlobalState, issue_annotation: IssueAnnotation
    ) -> bool:
        address = (
            issue_annotation.issue.source_location or issue_annotation.issue.address
        )
        return (
            issue_annotation.detector.swc_id,
            address,
            get_code_hash(global_state.environment.code.bytecode),
        ) in self.issue_cache

    def _check_issue(
        self, global_state: GlobalState, issue_annotation: IssueAnnotation
    ):
        if self.issue_in_cache(global_state, issue_annotation):
            return

        success = 0
        tx_seq = []
        for constraint in issue_annotation.conditions:
            condition = self._translate_condition(
                global_state,
                [constraint, deepcopy(keccak_function_manager.create_conditions())],
            )
            condition = [
                expr
                for expr in global_state.world_state.constraints.as_list + condition
            ]
            try:
                tx_seq = get_transaction_sequence(global_state, Constraints(condition))
                success += 1
            except UnsatError:
                break

        if success == len(issue_annotation.conditions):
            log.info("Found an issue")
            new_issue = copy(issue_annotation.issue)
            new_issue.transaction_sequence = tx_seq
            issue_annotation.detector.issues += [new_issue]
            addresss = (
                issue_annotation.issue.source_location or issue_annotation.issue.address
            )
            self.issue_cache.add(
                (
                    issue_annotation.detector.swc_id,
                    addresss,
                    get_code_hash(global_state.environment.code.bytecode),
                )
            )

    def _translate_condition(self, global_state: GlobalState, condition: List[Bool]):
        condition = deepcopy(condition)
        for account_id, account in global_state.world_state.accounts.items():
            for expression in condition:
                substitute_exprs(expression, account_id, account, global_state)

        return condition

    def _summary_exit(
        self, global_state: GlobalState, transaction: BaseTransaction, revert: bool
    ):
        """Handles logic for when the analysis reaches the summary exit

        This function populates self.summaries with the discovered symbolic summaries
        :param global_state: The state at the exit of the discovered symbolic summary
        """
        summary_annotation = self._get_and_remove_summary_tracking_annotation(
            global_state
        )
        if not summary_annotation:
            log.error("Missing Annotation")
            return

        self._record_symbolic_summary(
            global_state, summary_annotation, transaction, revert
        )

        self._restore_previous_state(global_state, summary_annotation)

    @staticmethod
    def _get_and_remove_summary_tracking_annotation(
        global_state: GlobalState,
    ) -> Optional[SummaryTrackingAnnotation]:
        """Retrieves symbolic summary from the global state"""
        summary_annotation: List[SummaryTrackingAnnotation] = list(
            global_state.get_annotations(SummaryTrackingAnnotation)
        )
        if len(summary_annotation) != 1:
            logging.warning(
                f"Unexpected number of summary tracking annotations found: {len(summary_annotation)}\nSkipping..."
            )

        summary_annotation: SummaryTrackingAnnotation = summary_annotation[0]
        global_state.annotations.remove(summary_annotation)
        return summary_annotation

    def _record_symbolic_summary(
        self,
        global_state: GlobalState,
        tracking_annotation: SummaryTrackingAnnotation,
        transaction: BaseTransaction,
        revert,
    ):
        """Records a summary between tracking_annotation.entry and global_state"""
        if (
            len(list(global_state.get_annotations(MutationAnnotation))) == 0
            and list(global_state.get_annotations(IssueAnnotation)) == 0
        ):
            return

        storage_mutations = []
        return_value = transaction.return_data
        set_map = {}
        get_map = {}
        for index, account in global_state.world_state.accounts.items():
            if account.storage._standard_storage not in [
                p[1] for p in tracking_annotation.storage_pairs
            ]:
                get_map[account.address] = account.storage.keys_get
                set_map[account.address] = account.storage.keys_set
                storage_mutations.append(
                    (index, copy(account.storage._standard_storage))
                )

        condition = global_state.world_state.constraints.get_all_constraints()
        for constraint in tracking_annotation.entry.world_state.constraints:
            condition.remove(constraint)
        annotations = list(global_state.get_annotations(IssueAnnotation))
        summary = SymbolicSummary(
            storage_effect=deepcopy(storage_mutations),
            balance_effect=copy(global_state.world_state.balances),
            condition=deepcopy(condition),
            return_value=return_value,
            entry=tracking_annotation.entry.mstate.pc,
            exit=global_state.mstate.pc,
            trace=tracking_annotation.trace,
            code=tracking_annotation.code,
            issues=list(global_state.get_annotations(IssueAnnotation)),
            revert=revert,
            get_map=get_map,
            set_map=set_map,
        )
        log.debug(list(global_state.get_annotations(IssueAnnotation)))
        # Calculate issues for the first transaction
        if len(global_state.world_state.transaction_sequence) == 2:
            for state in self.init_save_states:
                for issue in summary.issues:
                    self._check_issue(state, issue)

        self.summaries.append(summary)

    @classmethod
    def _restore_previous_state(
        cls, global_state: GlobalState, tracking_annotation: SummaryTrackingAnnotation
    ):
        """Restores the previous persistent variables to the global state"""
        for og_storage, sym_storage in tracking_annotation.storage_pairs:
            cls._rewrite(global_state, sym_storage, og_storage)

        cls._rewrite(
            global_state,
            tracking_annotation.balance_pair[1],
            tracking_annotation.balance_pair[0],
        )
        cls._restore_environment(tracking_annotation, global_state)

    @staticmethod
    def _rewrite(global_state: GlobalState, original: Expression, new: Expression):
        for account in global_state.world_state.accounts.values():
            account.storage._standard_storage.substitute(original, new)

        global_state.world_state.balances.substitute(original, new)

        for constraint in global_state.world_state.constraints:
            constraint.substitute(original, new)
