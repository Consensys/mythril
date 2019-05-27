import logging

from mythril.analysis.solver import get_model
from mythril.analysis.report import Issue
from mythril.laser.ethereum.state.annotation import StateAnnotation
from mythril.laser.ethereum.state.global_state import GlobalState
from mythril.laser.smt import get_variables_from_constraints
from mythril.analysis.swc_data import TX_ORDER_DEPENDENCE
from mythril.analysis.modules.base import DetectionModule
from mythril.exceptions import UnsatError


log = logging.getLogger(__name__)


class StorageAnnotation(StateAnnotation):
    def __init__(self, storage_state: GlobalState):
        self.storage_state = storage_state


def get_transitive_annotations(value, constraints):
    queue = [value]
    visited = set()
    visited.add(value)
    annotations = []
    for value in queue:
        annotations += value.annotations
        for constraint in constraints:
            var_list = list(get_variables_from_constraints(constraint))
            if value not in var_list:
                continue
            for var in var_list:
                if var not in queue:
                    continue
                visited.add(var)
                queue.append(var)
    return annotations


class TxOrderDependenceModule(DetectionModule):
    def __init__(self):
        super().__init__(
            name="Transaction Order Dependence",
            swc_id=TX_ORDER_DEPENDENCE,
            pre_hooks=["CALL", "STATICCALL", "CALLCODE", "SSTORE"],
            entrypoint="callback",
            description=(
                "This module finds the existance of transaction order dependence "
                "vulnerabilities. The following webpage contains an extensive description "
                "of the vulnerability: "
                "https://consensys.github.io/smart-contract-best-practices/known_attacks/#transaction-ordering-dependence-tod-front-running"
            ),
        )

    def execute(self, state: GlobalState):
        """ Executes the analysis module"""
        log.debug("Executing module: TOD")
        opcode = state.get_current_instruction()["opcode"]
        if opcode == "SSTORE":
            value = state.mstate.stack[-2]
            value.annotate(StorageAnnotation(state))
            state.mstate.stack[-2] = value
        value = state.mstate.stack[-3]
        annotations = get_transitive_annotations(value, state.mstate.constraints)
        for annotation in annotations:
            if not isinstance(annotation, StorageAnnotation):
                continue
            if int(annotation.storage_state.current_transaction.id) >= int(
                state.current_transaction.id
            ):
                continue
            try:
                get_model(
                    state.mstate.constraints
                    + [
                        state.current_transaction.caller
                        != annotation.storage_state.current_transaction.caller
                    ]
                )
            except UnsatError:
                continue
            description_tail = "A transaction order dependence vulnerability may exist in this contract. The value or target of the call statement is loaded from a writable storage location."

            issue = Issue(
                contract=state.environment.active_account.contract_name,
                function_name=state.environment.active_function_name,
                address=annotation.storage_state.environment.active_function_address,
                title="Transaction Order Dependence",
                bytecode=state.environment.code.bytecode,
                swc_id=TX_ORDER_DEPENDENCE,
                severity="Medium",
                description_head="The call outcome may depend on transaction order.",
                description_tail=description_tail,
                gas_used=(state.mstate.min_gas_used, state.mstate.max_gas_used),
            )
            self.issues.append(issue)
        return self.issues


detector = TxOrderDependenceModule()
