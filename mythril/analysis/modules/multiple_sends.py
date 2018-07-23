from mythril.analysis.report import Issue
"""
MODULE DESCRIPTION:

Check for multiple sends in a single transaction
"""


def execute(statespace):
    issues = []

    for call in statespace.calls:
        findings = []
        # explore state
        findings += _explore_states(call, statespace)
        # explore nodes
        findings += _explore_nodes(call, statespace)

        if len(findings) > 0:
            node = call.node
            instruction = call.state.get_current_instruction()
            issue = Issue(node.contract_name, node.function_name, instruction['address'],
                          "Multiple Calls",
                          "Information")

            issue.description = \
                "Multiple sends exist in one transaction, try to isolate each external call into its own transaction." \
                " As external calls can fail accidentally or deliberately.\nConsecutive calls: \n"

            for finding in findings:
                issue.description += \
                    "Call at address: {}\n".format(finding.state.get_current_instruction()['address'])

            issues.append(issue)
    return issues


def _explore_nodes(call, statespace):
    children = _child_nodes(statespace, call.node)
    sending_children = list(filter(lambda call: call.node in children, statespace.calls))
    return sending_children


def _explore_states(call, statespace):
    other_calls = list(
            filter(lambda other: other.node == call.node and other.state_index > call.state_index, statespace.calls)
        )
    return other_calls


def _child_nodes(statespace, node):
    result = []
    children = [statespace.nodes[edge.node_to] for edge in statespace.edges if edge.node_from == node.uid]

    for child in children:
        result.append(child)
        result += _child_nodes(statespace, child)

    return result
