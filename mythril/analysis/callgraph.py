import re

from jinja2 import Environment, PackageLoader, select_autoescape
from laser.ethereum.svm import NodeFlags
import z3

default_opts = {
    'autoResize': True,
    'height': '100%',
    'width': '100%',
    'manipulation': False,
    'layout': {
        'improvedLayout': True,
        'hierarchical': {
            'enabled': True,
            'levelSeparation': 450,
            'nodeSpacing': 200,
            'treeSpacing': 100,
            'blockShifting': True,
            'edgeMinimization': True,
            'parentCentralization': False,
            'direction': 'LR',
            'sortMethod': 'directed'
        }
    },
    'nodes': {
        'color': '#000000',
        'borderWidth': 1,
        'borderWidthSelected': 2,
        'chosen': True,
        'shape': 'box',
        'font': {'align': 'left', 'color': '#FFFFFF'},
    },
    'edges': {
        'font': {
            'color': '#FFFFFF',
            'face': 'arial',
            'background': 'none',
            'strokeWidth': 0,
            'strokeColor': '#ffffff',
            'align': 'horizontal',
            'multi': False,
            'vadjust': 0,
        }
    },
    'physics': {'enabled': False}
}

phrack_opts = {
    'nodes': {
        'color': '#000000',
        'borderWidth': 1,
        'borderWidthSelected': 1,
        'shapeProperties': {
            'borderDashes': False,
            'borderRadius': 0,
        },
        'chosen': True,
        'shape': 'box',
        'font': {'face': 'courier new', 'align': 'left', 'color': '#000000'},
    },
    'edges': {
        'font': {
            'color': '#000000',
            'face': 'courier new',
            'background': 'none',
            'strokeWidth': 0,
            'strokeColor': '#ffffff',
            'align': 'horizontal',
            'multi': False,
            'vadjust': 0,
        }
    }
}

default_colors = [
    {'border': '#26996f', 'background': '#2f7e5b', 'highlight': {'border': '#26996f', 'background': '#28a16f'}},
    {'border': '#9e42b3', 'background': '#842899', 'highlight': {'border': '#9e42b3', 'background': '#933da6'}},
    {'border': '#b82323', 'background': '#991d1d', 'highlight': {'border': '#b82323', 'background': '#a61f1f'}},
    {'border': '#4753bf', 'background': '#3b46a1', 'highlight': {'border': '#4753bf', 'background': '#424db3'}},
    {'border': '#26996f', 'background': '#2f7e5b', 'highlight': {'border': '#26996f', 'background': '#28a16f'}},
    {'border': '#9e42b3', 'background': '#842899', 'highlight': {'border': '#9e42b3', 'background': '#933da6'}},
    {'border': '#b82323', 'background': '#991d1d', 'highlight': {'border': '#b82323', 'background': '#a61f1f'}},
    {'border': '#4753bf', 'background': '#3b46a1', 'highlight': {'border': '#4753bf', 'background': '#424db3'}},
]

phrack_color = {'border': '#000000', 'background': '#ffffff',
                'highlight': {'border': '#000000', 'background': '#ffffff'}}


def extract_nodes(statespace, color_map):
    nodes = []
    for node_key in statespace.nodes:
        node = statespace.nodes[node_key]
        instructions = [state.get_current_instruction() for state in node.states]
        code_split = []
        for instruction in instructions:
            if instruction['opcode'].startswith("PUSH"):
                code_line = "%d %s %s" % (instruction['address'], instruction['opcode'], instruction['argument'])
            elif instruction['opcode'].startswith("JUMPDEST") and NodeFlags.FUNC_ENTRY in node.flags and instruction['address'] == node.start_addr:
                code_line = node.function_name
            else:
                code_line = "%d %s" % (instruction['address'], instruction['opcode'])

            code_line = re.sub("([0-9a-f]{8})[0-9a-f]+", lambda m: m.group(1) + "(...)", code_line)
            code_split.append(code_line)

        truncated_code = '\n'.join(code_split) if (len(code_split) < 7) \
            else '\n'.join(code_split[:6]) + "\n(click to expand +)"

        nodes.append({
            'id': str(node_key),
            'color': color_map[node.get_cfg_dict()['contract_name']],
            'size': 150,
            'fullLabel': '\n'.join(code_split),
            'label': truncated_code,
            'truncLabel': truncated_code,
            'isExpanded': False
        })
    return nodes


def extract_edges(statespace):
    edges = []
    for edge in statespace.edges:
        if edge.condition is None:
            label = ""
        else:
            try:
                label = str(z3.simplify(edge.condition)).replace("\n", "")
            except z3.Z3Exception:
                label = str(edge.condition).replace("\n", "")

        label = re.sub(r'([^_])([\d]{2}\d+)', lambda m: m.group(1) + hex(int(m.group(2))), label)

        edges.append({
            'from': str(edge.as_dict()['from']),
            'to': str(edge.as_dict()['to']),
            'arrows': 'to',
            'label': label,
            'smooth': {'type': 'cubicBezier'}
        })
    return edges


def generate_graph(statespace, title="Mythril / Ethereum LASER Symbolic VM", physics=False, phrackify=False):
    env = Environment(loader=PackageLoader('mythril.analysis'), autoescape=select_autoescape(['html', 'xml']))
    template = env.get_template('callgraph.html')

    graph_opts = default_opts
    accounts = statespace.accounts

    if phrackify:
        color_map = {accounts[k].contract_name: phrack_color for k in accounts}
        graph_opts.update(phrack_opts)
    else:
        color_map = {accounts[k].contract_name: default_colors[i % len(default_colors)] for i, k in enumerate(accounts)}

    graph_opts['physics']['enabled'] = physics

    return template.render(title=title,
                           nodes=extract_nodes(statespace, color_map),
                           edges=extract_edges(statespace),
                           phrackify=phrackify,
                           opts=graph_opts
                           )
