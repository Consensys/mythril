import logging
import re
import copy

from mythril.analysis import solver
from mythril.analysis.ops import *
from mythril.analysis.report import Issue
from mythril.analysis.swc_data import TX_ORDER_DEPENDENCE
from mythril.analysis.modules.base import DetectionModule
from mythril.exceptions import UnsatError


log = logging.getLogger(__name__)


class TxOrderDependenceModule(DetectionModule):
    def __init__(self):
        super().__init__(
            name="Transaction Order Dependence",
            swc_id=TX_ORDER_DEPENDENCE,
            description=(
                "This module finds the existance of transaction order dependence "
                "vulnerabilities. The following webpage contains an extensive description "
                "of the vulnerability: "
                "https://consensys.github.io/smart-contract-best-practices/known_attacks/#transaction-ordering-dependence-tod-front-running"
            ),
        )

    def execute(self, statespace):
        """ Executes the analysis module"""
        log.debug("Executing module: TOD")

        issues = []

        for call in statespace.calls:
            # Do analysis
            interesting_storages = list(self._get_influencing_storages(call))
            changing_sstores = list(
                self._get_influencing_sstores(statespace, interesting_storages)
            )

            description_tail = (
                "A transaction order dependence vulnerability may exist in this contract. The value or "
                "target of the call statement is loaded from a writable storage location."
            )

            # Build issue if necessary
            if len(changing_sstores) > 0:
                node = call.node
                instruction = call.state.get_current_instruction()
                issue = Issue(
                    contract=node.contract_name,
                    function_name=node.function_name,
                    address=instruction["address"],
                    title="Transaction Order Dependence",
                    bytecode=call.state.environment.code.bytecode,
                    swc_id=TX_ORDER_DEPENDENCE,
                    severity="Medium",
                    description_head="The call outcome may depend on transaction order.",
                    description_tail=description_tail,
                    gas_used=(
                        call.state.mstate.min_gas_used,
                        call.state.mstate.max_gas_used,
                    ),
                )


                issues.append(issue)

        return issues

    # TODO: move to __init__ or util module
    def _get_states_with_opcode(self, statespace, opcode):
        """ Gets all (state, node) tuples in statespace with opcode"""
        for k in statespace.nodes:
            node = statespace.nodes[k]
            for state in node.states:
                if state.get_current_instruction()["opcode"] == opcode:
                    yield state, node

    def _dependent_on_storage(self, expression):
        """ Checks if expression is dependent on a storage symbol and returns the influencing storages"""
        pattern = re.compile(r"storage_[a-z0-9_&^]*[0-9]+")
        return pattern.findall(str(simplify(expression)))

    def _get_storage_variable(self, storage, state):
        """
        Get storage z3 object given storage name and the state
        :param storage: storage name example: storage_0
        :param state: state to retrieve the variable from
        :return: z3 object representing storage
        """
        index = int(re.search("[0-9]+", storage).group())
        try:
            return state.environment.active_account.storage[index]
        except KeyError:
            return None

    def _can_change(self, constraints, variable):
        """ Checks if the variable can change given some constraints """
        _constraints = copy.deepcopy(constraints)
        try:
            model = solver.get_model(_constraints)
        except UnsatError:
            return False
        try:
            initial_value = int(str(model.eval(variable, model_completion=True)))
            return (
                self._try_constraints(constraints, [variable != initial_value])
                is not None
            )
        except AttributeError:
            return False

    def _get_influencing_storages(self, call):
        """ Examines a Call object and returns an iterator of all storages that influence the call value or direction"""
        state = call.state
        node = call.node

        # Get relevant storages
        to, value = call.to, call.value
        storages = []
        if to.type == VarType.SYMBOLIC:
            storages += self._dependent_on_storage(to.val)
        if value.type == VarType.SYMBOLIC:
            storages += self._dependent_on_storage(value.val)

        # See if they can change within the constraints of the node
        for storage in storages:
            variable = self._get_storage_variable(storage, state)
            can_change = self._can_change(node.constraints, variable)
            if can_change:
                yield storage

    def _get_influencing_sstores(self, statespace, interesting_storages):
        """ Gets sstore (state, node) tuples that write to interesting_storages"""
        for sstore_state, node in self._get_states_with_opcode(statespace, "SSTORE"):
            index, value = sstore_state.mstate.stack[-1], sstore_state.mstate.stack[-2]
            try:
                index = util.get_concrete_int(index)
            except TypeError:
                index = str(index)
            if "storage_{}".format(index) not in interesting_storages:
                continue

            yield sstore_state, node

    # TODO: remove
    def _try_constraints(self, constraints, new_constraints):
        """
        Tries new constraints
        :return Model if satisfiable otherwise None
        """
        _constraints = copy.deepcopy(constraints)
        for constraint in new_constraints:
            _constraints.append(copy.deepcopy(constraint))
        try:
            model = solver.get_model(_constraints)
            return model
        except UnsatError:
            return None


detector = TxOrderDependenceModule()
