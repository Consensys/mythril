from ethjsonrpc import EthJsonRpc


class EthJsonRpcWithDebug(EthJsonRpc):

    def getBlockRlp(self, number=0):

        return self._call('debug_getBlockRlp', [number])

    def traceTransaction(self, txHash):

        return self._call('debug_traceTransaction', [txHash])
