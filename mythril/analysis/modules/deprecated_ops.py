from mythril.analysis.report import Issue
from mythril.analysis.swc_data import TX_ORIGIN_USAGE
from mythril.analysis.modules.base import DetectionModule
import logging


"""
MODULE DESCRIPTION:

Check for constraints on tx.origin (i.e., access to some functionality is restricted to a specific origin).
"""


class DeprecatedOperationsModule(DetectionModule):
    def __init__(self):
        super().__init__(
            name="Deprecated Operations",
            swc_id=TX_ORIGIN_USAGE,
            hooks=["ORIGIN"],
            description=(
                "Check for constraints on tx.origin (i.e., access to some "
                "functionality is restricted to a specific origin)."
            ),
        )

    def execute(self, statespace):

        logging.debug("Executing module: DEPRECATED OPCODES")

        issues = []

        for k in statespace.nodes:
            node = statespace.nodes[k]

            for state in node.states:

                instruction = state.get_current_instruction()

                if instruction["opcode"] == "ORIGIN":
                    description = (
                        "The function `{}` retrieves the transaction origin (tx.origin) using the ORIGIN opcode. "
                        "Use msg.sender instead.\nSee also: "
                        "https://solidity.readthedocs.io/en/develop/security-considerations.html#tx-origin".format(
                            node.function_name
                        )
                    )

                    issue = Issue(
                        contract=node.contract_name,
                        function_name=node.function_name,
                        address=instruction["address"],
                        title="Use of tx.origin",
                        bytecode=state.environment.code.bytecode,
                        _type="Warning",
                        swc_id=TX_ORIGIN_USAGE,
                        description=description,
                    )
                    issues.append(issue)

        return issues


detector = DeprecatedOperationsModule()
