import re

from jinja2 import Environment, PackageLoader, select_autoescape
from laser.ethereum.svm import NodeFlags
from z3 import Z3Exception, simplify

default_opts = {
    'autoResize': True,
    'height': '100%',
    'width': '100%',
    'manipulation': False,
    'height': '90%',
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

        code = node.get_cfg_dict()['code']
        code = re.sub("([0-9a-f]{8})[0-9a-f]+", lambda m: m.group(1) + "(...)", code)

        if NodeFlags.FUNC_ENTRY in node.flags:
            code = re.sub("JUMPDEST", node.function_name, code)

        code_split = code.split("\\n")
        code_split = [x for x in code_split if x]
        full_code = '\n'.join(code_split)

        truncated_code = '\n'.join(code_split) if (len(code_split) < 7) else '\n'.join(code_split[:6]) + "\n(click to expand +)"

        color = color_map[node.get_cfg_dict()['contract_name']]

        nodes.append({
            'id': str(node_key),
            'color': color,
            'size': 150,
            'label': truncated_code,
            'fullLabel': full_code,
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
                label = str(simplify(edge.condition)).replace("\n", "")
            except Z3Exception:
                label = str(edge.condition).replace("\n", "")

        label = re.sub("([^_])([\d]{2}\d+)", lambda m: m.group(1) + hex(int(m.group(2))), label)

        edges.append({
            'from': str(edge.as_dict()['from']),
            'to': str(edge.as_dict()['to']),
            'arrows': 'to',
            'label': label,
            'smooth': {'type': 'cubicBezier'}
        })
    return edges


def generate_graph(statespace, physics=False, phrackify=False, opts=None):
    '''
    This is some of the the ugliest code in the whole project.
    At some point someone needs to write a templating system.
    '''

    if opts is None:
        opts = {}
    env = Environment(
        loader=PackageLoader('mythril.analysis'),
        autoescape=select_autoescape(['html', 'xml'])
    )
    template = env.get_template('graph.html')

    color_map = {}
    graph_opts = default_opts

    if phrackify:
        graph_opts.update(phrack_opts)
        for k in statespace.accounts:
            color_map[statespace.accounts[k].contract_name] = phrack_color
    else:
        i = 0
        for k in statespace.accounts:
            color_map[statespace.accounts[k].contract_name] = default_colors[i]
            i += 1

    graph_opts.update(opts)
    graph_opts['physics']['enabled'] = physics

    nodes = extract_nodes(statespace, color_map)

    return template.render(title="Mythril / Ethereum LASER Symbolic VM",
                           nodes=extract_nodes(statespace, color_map),
                           edges=extract_edges(statespace),
                           phrackify=phrackify,
                           opts=graph_opts
                           )
