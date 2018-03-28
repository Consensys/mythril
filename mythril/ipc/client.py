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
        self.socket = None
        self.connect()

    def connect(self):
        self.close()
        self.socket = self.get_socket()

    def close(self):
        if self.socket is not None:
            try:
                self.socket.close()
            except socket.error:
                pass

    def get_socket(self):
        _socket = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
        _socket.connect(self.ipc_path)
        # Tell the socket not to block on reads.
        _socket.settimeout(2)
        return _socket

    def read_response(self):
        response_raw = ""
        while True:
            response_raw += to_text(self.socket.recv(4096))
            # print("response_raw: " + response_raw)
            trimmed = response_raw.strip()
            if trimmed and trimmed[-1] == '}':
                try:
                    return json.loads(trimmed)
                except JSONDecodeError:
                    continue

    def _call(self, method, params=None, _id=1):
        params = params or []
        data = {
            'jsonrpc': '2.0',
            'method': method,
            'params': params,
            'id': _id,
        }
        request = to_bytes(json.dumps(data))

        for _ in range(3):
            self.socket.sendall(request)
            try:
                response = self.read_response()
                break
            except socket.timeout:
                self.connect()
        else:
            raise ValueError("No JSON returned by socket")

        if "error" in response:
            raise ValueError(response["error"]["message"])

        return response["result"]
