from mythril.laser.smt import BaseArray, Array, Solver, symbol_factory
from mythril.support.support_args import args
from mythril.laser.ethereum.state.global_state import GlobalState
from mythril.laser.plugin.plugins.plugin_annotations import MutationAnnotation
from copy import deepcopy

import logging
import z3

log = logging.getLogger(__name__)


class SymbolicSummary:
    """Symbolic Summary

    A symbolic summary is an awesome construct that allows mythril to record and re-use partial analysis results
    """

    def __init__(
        self,
        storage_effect,
        balance_effect,
        condition,
        return_value,
        entry,
        exit,
        trace,
        code,
        issues,
        revert,
        set_map=None,
        get_map=None,
    ):
        self.storage_effect = storage_effect
        self.balance_effect = balance_effect
        self.condition = condition
        self.return_value = return_value
        self.entry = entry
        self.exit = exit
        self.trace = trace
        self.code = code
        self.issues = issues
        self.revert = revert
        self.set_map = set_map
        self.get_map = get_map

    @property
    def as_csv(self, delimiter=",", sub_array_delimiter=";", tuple_delimiter=":"):
        condition = sub_array_delimiter.join(map(str, self.condition))
        storage_effect = sub_array_delimiter.join(
            [f"{ap[0]}{tuple_delimiter}{ap[1]}" for ap in self.storage_effect]
        )
        return_value = None
        trace = sub_array_delimiter.join(map(str, self.trace))
        return (
            delimiter.join(
                map(
                    str,
                    [
                        self.entry,
                        condition,
                        self.exit,
                        storage_effect,
                        return_value,
                        trace,
                    ],
                )
            )
            .replace("\n", "")
            .replace(" ", "")
        )

    @property
    def as_dict(self):
        return dict(
            entry=self.entry,
            condition=list(map(str, self.condition)),
            exit=self.exit,
            storage_effect=list(map(str, self.storage_effect)),
            balance_effect=str(self.balance_effect),
            return_value=self.return_value,
            trace=self.trace[:],
            code=self.code,
            issues=len(self.issues),
            revert=self.revert,
        )

    def apply_summary(self, global_state: GlobalState):

        # Copy and apply summary
        global_state = deepcopy(global_state)
        conditions = deepcopy(self.condition)
        for account_id, account in global_state.world_state.accounts.items():
            for expression in conditions:
                substitute_exprs(expression, account_id, account, global_state)

        for account_id, effect in self.storage_effect:
            account = global_state.world_state.accounts[account_id]
            new_storage = deepcopy(effect)
            substitute_exprs(new_storage, account_id, account, global_state)
            account.storage._standard_storage = new_storage

        new_balances = deepcopy(self.balance_effect)
        new_balances.substitute(
            Array("summary_balance", 256, 256), global_state.world_state.balances
        )
        global_state.world_state.balances = new_balances

        # Set constraints
        global_state.world_state.constraints += [c for c in conditions]

        # Check Condition
        solver = Solver()
        solver.set_timeout(args.solver_timeout)
        solver.add(*(global_state.world_state.constraints.as_list))
        sat = solver.check() == z3.sat

        if not sat:
            return []

        global_state.node.constraints = global_state.world_state.constraints
        global_state.world_state.node = global_state.node
        global_state.annotate(MutationAnnotation())
        return [global_state]


def substitute_exprs(expression, account_id, account, global_state):

    a = Array("2_calldata", 256, 8)
    b = Array(f"{global_state.current_transaction.id}_calldata", 256, 8)
    expression.substitute(a, b)
    a = symbol_factory.BitVecSym("2_calldatasize", 256)
    b = symbol_factory.BitVecSym(
        f"{global_state.current_transaction.id}_calldatasize", 256
    )
    expression.substitute(a, b)
    a = symbol_factory.BitVecSym("sender_2", 256)
    b = symbol_factory.BitVecSym(f"sender_{global_state.current_transaction.id}", 256)
    expression.substitute(a, b)
    a = symbol_factory.BitVecSym("call_value2", 256)
    b = symbol_factory.BitVecSym(
        f"call_value{global_state.current_transaction.id}", 256
    )
    expression.substitute(a, b)
    a = Array(f"{account_id}_symbolic_storage", 256, 256)
    b = account.storage._standard_storage
    expression.substitute(a, b)

    a = Array("summary_balance", 256, 256)
    b = global_state.world_state.balances
    expression.substitute(a, b)
