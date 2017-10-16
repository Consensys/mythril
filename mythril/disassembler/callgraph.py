from laser.ethereum import svm, cfg

def generate_callgraph(disassembly, file):

    _svm = svm.SVM(disassembly)

    _svm.sym_exec()

    cfg.generate_callgraph(_svm, file)
