from mythril.analysis.report import Issue
from mythril.analysis.swc_data import MULTIPLE_SENDS
from mythril.analysis.modules.base import DetectionModule
from mythril.laser.ethereum.cfg import JumpType


class MultipleSendsModule(DetectionModule):
    """This module checks for multiple sends in a single transaction."""
    def __init__(self):
        super().__init__(
            name="Multiple Sends",
            swc_id=MULTIPLE_SENDS,
            hooks=["CALL", "DELEGATECALL", "STATICCALL", "CALLCODE"],
            description="Check for multiple sends in a single transaction",
        )

    def execute(self, statespace):
        """

        :param statespace:
        :return:
        """
        issues = []

        for call in statespace.calls:
            findings = []
            # explore state
            findings += self._explore_states(call, statespace)
            # explore nodes
            findings += self._explore_nodes(call, statespace)

            if len(findings) > 0:
                node = call.node
                instruction = call.state.get_current_instruction()
                issue = Issue(
                    contract=node.contract_name,
                    function_name=node.function_name,
                    address=instruction["address"],
                    swc_id=MULTIPLE_SENDS,
                    bytecode=call.state.environment.code.bytecode,
                    title="Multiple Calls",
                    _type="Informational",
                    gas_used=(
                        call.state.mstate.min_gas_used,
                        call.state.mstate.max_gas_used,
                    ),
                )

                issue.description = (
                    "Multiple sends are executed in a single transaction. "
                    "Try to isolate each external call into its own transaction,"
                    " as external calls can fail accidentally or deliberately.\nConsecutive calls: \n"
                )

                for finding in findings:
                    issue.description += "Call at address: {}\n".format(
                        finding.state.get_current_instruction()["address"]
                    )

                issues.append(issue)
        return issues

    def _explore_nodes(self, call, statespace):
        children = self._child_nodes(statespace, call.node)
        sending_children = list(filter(lambda c: c.node in children, statespace.calls))
        return sending_children

    @staticmethod
    def _explore_states(call, statespace):
        other_calls = list(
            filter(
                lambda other: other.node == call.node
                and other.state_index > call.state_index,
                statespace.calls,
            )
        )
        return other_calls

    def _child_nodes(self, statespace, node):
        result = []
        children = [
            statespace.nodes[edge.node_to]
            for edge in statespace.edges
            if edge.node_from == node.uid and edge.type != JumpType.Transaction
        ]

        for child in children:
            result.append(child)
            result += self._child_nodes(statespace, child)

        return result


detector = MultipleSendsModule()
