"""This module provides a function to convert a state space into a set of state
nodes and transition edges."""
from z3 import Z3Exception
from mythril.laser.smt import simplify
from mythril.laser.ethereum.svm import NodeFlags
import re

colors = [
    {
        "border": "#26996f",
        "background": "#2f7e5b",
        "highlight": {"border": "#fff", "background": "#28a16f"},
    },
    {
        "border": "#9e42b3",
        "background": "#842899",
        "highlight": {"border": "#fff", "background": "#933da6"},
    },
    {
        "border": "#b82323",
        "background": "#991d1d",
        "highlight": {"border": "#fff", "background": "#a61f1f"},
    },
    {
        "border": "#4753bf",
        "background": "#3b46a1",
        "highlight": {"border": "#fff", "background": "#424db3"},
    },
    {
        "border": "#26996f",
        "background": "#2f7e5b",
        "highlight": {"border": "#fff", "background": "#28a16f"},
    },
    {
        "border": "#9e42b3",
        "background": "#842899",
        "highlight": {"border": "#fff", "background": "#933da6"},
    },
    {
        "border": "#b82323",
        "background": "#991d1d",
        "highlight": {"border": "#fff", "background": "#a61f1f"},
    },
    {
        "border": "#4753bf",
        "background": "#3b46a1",
        "highlight": {"border": "#fff", "background": "#424db3"},
    },
]


def get_serializable_statespace(statespace):
    """

    :param statespace:
    :return:
    """
    nodes = []
    edges = []

    color_map = {}
    i = 0
    for k in statespace.accounts:
        color_map[statespace.accounts[k].contract_name] = colors[i]
        i += 1

    for node_key in statespace.nodes:

        node = statespace.nodes[node_key]

        code = node.get_cfg_dict()["code"]
        code = re.sub("([0-9a-f]{8})[0-9a-f]+", lambda m: m.group(1) + "(...)", code)

        if NodeFlags.FUNC_ENTRY in node.flags:
            code = re.sub("JUMPDEST", node.function_name, code)

        code_split = code.split("\\n")

        truncated_code = (
            code
            if (len(code_split) < 7)
            else "\\n".join(code_split[:6]) + "\\n(click to expand +)"
        )
        try:
            color = color_map[node.get_cfg_dict()["contract_name"]]
        except KeyError:
            color = colors[i]
            i += 1
            color_map[node.get_cfg_dict()["contract_name"]] = color

        def get_state_accounts(node_state):
            """

            :param node_state:
            :return:
            """
            state_accounts = []
            for key in node_state.accounts:
                account = node_state.accounts[key].as_dict
                account.pop("code", None)
                account["balance"] = str(account["balance"])

                storage = {}
                for storage_key in account["storage"].printable_storage:
                    storage[str(storage_key)] = str(account["storage"][storage_key])

                state_accounts.append({"address": key, "storage": storage})
            return state_accounts

        states = [
            {"machine": x.mstate.as_dict, "accounts": get_state_accounts(x)}
            for x in node.states
        ]

        for state in states:
            state["machine"]["stack"] = [str(s) for s in state["machine"]["stack"]]
            state["machine"]["memory"] = [
                str(m)
                for m in state["machine"]["memory"][: len(state["machine"]["memory"])]
            ]

        truncated_code = truncated_code.replace("\\n", "\n")
        code = code.replace("\\n", "\n")

        s_node = {
            "id": str(node_key),
            "func": str(node.function_name),
            "label": truncated_code,
            "code": code,
            "truncated": truncated_code,
            "states": states,
            "color": color,
            "instructions": code.split("\n"),
        }

        nodes.append(s_node)

    for edge in statespace.edges:

        if edge.condition is None:
            label = ""
        else:

            try:
                label = str(simplify(edge.condition)).replace("\n", "")
            except Z3Exception:
                label = str(edge.condition).replace("\n", "")

        label = re.sub(
            "([^_])([\d]{2}\d+)", lambda m: m.group(1) + hex(int(m.group(2))), label
        )
        code = re.sub("([0-9a-f]{8})[0-9a-f]+", lambda m: m.group(1) + "(...)", code)

        s_edge = {
            "from": str(edge.as_dict["from"]),
            "to": str(edge.as_dict["to"]),
            "arrows": "to",
            "label": label,
            "smooth": {"type": "cubicBezier"},
        }

        edges.append(s_edge)

    return {"edges": edges, "nodes": nodes}
