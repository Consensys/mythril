import json
import socket

from mythril.rpc.base_client import BaseClient
from .utils import (get_default_ipc_path, to_text, to_bytes)

try:
    from json import JSONDecodeError
except ImportError:
    JSONDecodeError = ValueError

IPC_PATH = None

'''
This code is mostly adapted from:
- https://github.com/ConsenSys/ethjsonrpc
- https://github.com/pipermerriam/ethereum-ipc-client
- https://github.com/ethereum/web3.py
'''


class EthIpc(BaseClient):

    def __init__(self, ipc_path=IPC_PATH, testnet=False):
        if ipc_path is None:
            ipc_path = get_default_ipc_path(testnet)
        self.ipc_path = ipc_path

    def get_socket(self):
        _socket = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
        _socket.connect(self.ipc_path)
        # Tell the socket not to block on reads.
        _socket.settimeout(0.2)
        return _socket

    def _call(self, method, params=None, _id=1):
        params = params or []
        data = {
            'jsonrpc': '2.0',
            'method': method,
            'params': params,
            'id': _id,
        }
        request = to_bytes(json.dumps(data))
        _socket = self.get_socket()

        for _ in range(3):
            _socket.sendall(request)
            response_raw = ""

            while True:
                try:
                    response_raw += to_text(_socket.recv(4096))
                except socket.timeout:
                    break

            if response_raw == "":
                _socket.close()
                _socket = self.get_socket()
                continue

            _socket.close()

            break
        else:
            raise ValueError("No JSON returned by socket")

        response = json.loads(response_raw)

        if "error" in response:
            raise ValueError(response["error"]["message"])

        return response["result"]
