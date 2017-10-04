import graphviz as gv


styles = {
    'graph': {
        'overlap': 'false',
        'fontsize': '16',
        'fontcolor': 'white',
        'bgcolor': '#333333',
        'concentrate':'true',
    },
    'nodes': {
        'fontname': 'Helvetica',
        'shape': 'box',
        'fontcolor': 'white',
        'color': 'white',
        'style': 'filled',
        'fillcolor': '#006699',
    },
    'edges': {
        'style': 'dashed',
        'dir': 'forward',
        'color': 'white',
        'arrowhead': 'normal',
        'fontname': 'Courier',
        'fontsize': '12',
        'fontcolor': 'white',
    }
}

def apply_styles(graph, styles):
    graph.graph_attr.update(
        ('graph' in styles and styles['graph']) or {}
    )
    graph.node_attr.update(
        ('nodes' in styles and styles['nodes']) or {}
    )
    graph.edge_attr.update(
        ('edges' in styles and styles['edges']) or {}
    )
    return graph


def generate_callgraph(disassembly, file):

	graph = gv.Graph(format='svg')

	index = 0

	for block in disassembly.blocks:
		easm = block.get_easm().replace("\n", "\l")

		graph.node(str(index), easm)
		index += 1

	for xref in disassembly.xrefs:

		graph.edge(str(xref[0]), str(xref[1]))


	graph = apply_styles(graph, styles)

	graph.render(file)

