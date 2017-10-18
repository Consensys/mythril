from laser.ethereum import svm


graph_html = '''<html>
 <head>
  <style type="text/css">
   #mynetwork {
    background-color: #000000;
   }

   body {
    background-color: #000000;
    color: #ffffff;
   }
  </style>
  <link href="https://cdnjs.cloudflare.com/ajax/libs/vis/4.21.0/vis.min.css" rel="stylesheet" type="text/css" />
  <script src="https://cdnjs.cloudflare.com/ajax/libs/vis/4.21.0/vis.min.js"></script>
  <script>

    var options = {
      autoResize: true,
      height: '100%',
      width: '100%',
      manipulation: false,
      height: '90%',
      layout: {
        randomSeed: undefined,
        improvedLayout:true,
        hierarchical: {
          enabled:true,
          levelSeparation: 500,
          nodeSpacing: 200,
          treeSpacing: 100,
          blockShifting: true,
          edgeMinimization: true,
          parentCentralization: false,
          direction: 'LR',        // UD, DU, LR, RL
          sortMethod: 'directed'   // hubsize, directed
        }
      },
      nodes:{
        borderWidth: 1,
        borderWidthSelected: 2,
        chosen: true,
        shape: 'box',
        font: {
          align: 'left',
          color: '#FFFFFF',
        },
        color: {
          border: '#26996f',
          background: '#1f7e5b',
          highlight: {
            border: '#26996f',
            background: '#28a16f'
          }  
        }
      },
      edges:{
        font: {
          color: '#ffffff',
          size: 12, // px
          face: 'arial',
          background: 'none',
          strokeWidth: 0, // px
          strokeColor: '#ffffff',
          align: 'horizontal',
          multi: false,
          vadjust: 0,
        }
      },

      physics:{
        enabled: true,
      }   
    
  }

  [JS]

  </script>
 </head>
<body>
<p>Mythril / Ethereum LASER Symbolic VM</p>
<p><div id="mynetwork"></div><br /></p>
<script type="text/javascript">
var container = document.getElementById('mynetwork');
var data = {'nodes': nodes, 'edges': edges}
var gph = new vis.Network(container, data, options);
</script>
</body>
</html>
'''


def serialize(_svm):

    nodes = []
    edges = []

    for n in _svm.nodes:

        nodes.append("{id: " + str(_svm.nodes[n].as_dict()['id']) + ", size: 150, 'label': '" + _svm.nodes[n].as_dict()['code'] + "'}")

    for e in _svm.edges:

        edges.append("{from: " + str(e.as_dict()['from']) + ', to: ' + str(e.as_dict()['to']) + ", 'arrows': 'to', 'label': '" + str(e.condition).replace("\n", "") + "', 'smooth': {'type': 'cubicBezier'}}")

    return "var nodes = [\n" + ",\n".join(nodes) + "\n];\nvar edges = [\n" + ",\n".join(edges) + "\n];"



def generate_callgraph(disassembly, file):

    _svm = svm.SVM(disassembly)

    _svm.sym_exec()

    html = graph_html.replace("[JS]", serialize(_svm))

    print(html)
