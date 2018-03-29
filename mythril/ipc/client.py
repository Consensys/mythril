import json
import socket

from mythril.rpc.base_client import BaseClient
from .utils import (get_default_ipc_path, to_text, to_bytes)
import threading

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

# use thread local to store socket which will be reused just in owner thread
THREAD_LOCAL = threading.local()

class EthIpc(BaseClient):

    def __init__(self, ipc_path=IPC_PATH, testnet=False):
        if ipc_path is None:
            ipc_path = get_default_ipc_path(testnet)
        self.ipc_path = ipc_path

    def connect_if_not_yet(self):
        if not hasattr(THREAD_LOCAL, "socket"):
            THREAD_LOCAL.socket = self.get_socket()

    def reconnect(self):
        self.close()
        THREAD_LOCAL.socket = self.get_socket()

    @staticmethod
    def close():
        if THREAD_LOCAL.socket is not None:
            try:
                THREAD_LOCAL.socket.close()
            except socket.error:
                pass

    def get_socket(self):
        _socket = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
        _socket.connect(self.ipc_path)
        # Tell the socket not to block on reads.
        _socket.settimeout(2)
        return _socket

    @staticmethod
    def send_request(request):
        THREAD_LOCAL.socket.sendall(request)

    @staticmethod
    def read_response():
        response_raw = ""
        while True:
            response_raw += to_text(THREAD_LOCAL.socket.recv(4096))
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

        self.connect_if_not_yet()

        for _ in range(3):
            try:
                self.send_request(request)
                response = self.read_response()
                break
            except socket.timeout or OSError:
                self.reconnect()
        else:
            raise ValueError("No JSON returned by socket")

        if "error" in response:
            raise ValueError(response["error"]["message"])

        return response["result"]
