import json
import socket
import logging
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

    def __init__(self, ipc_path=IPC_PATH, testnet=False, socket_timeout=0.2):
        if ipc_path is None:
            ipc_path = get_default_ipc_path(testnet)
        self.ipc_path = ipc_path
        self.socket_timeout = socket_timeout

    def get_socket(self):
        _socket = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
        _socket.connect(self.ipc_path)
        # Tell the socket not to block on reads.
        _socket.settimeout(self.socket_timeout)
        return _socket

    def send(self, request):
        _socket = None
        try:
            _socket = self.get_socket()
            _socket.sendall(request)
            response_raw = ""

            while True:
                try:
                    response_raw += to_text(_socket.recv(4096))
                except socket.timeout:
                    break

            if response_raw == "":
                return None
            else:
                return response_raw
        finally:
            if _socket:
                _socket.close()

    def _call(self, method, params=None, _id=1):
        params = params or []
        data = {
            'jsonrpc': '2.0',
            'method': method,
            'params': params,
            'id': _id,
        }
        logging.debug("ipc send: %s" % json.dumps(data))
        request = to_bytes(json.dumps(data))

        for _ in range(3):
            response_raw = self.send(request)
            if response_raw is not None:
                break
        else:
            raise ValueError("No JSON returned by socket")

        logging.debug("ipc response: %s" % response_raw)
        response = json.loads(response_raw)

        if "error" in response:
            raise ValueError(response["error"]["message"])

        return response["result"]
