#!/usr/bin/env python3
# -*- coding: UTF-8 -*-
# Author : <github.com/tintinweb>

from werkzeug.wrappers import Request, Response
from werkzeug.serving import run_simple
from jsonrpc import JSONRPCResponseManager, dispatcher

from threading import Thread

import json

@dispatcher.add_method
def fire_lasers(**kwargs):
    if not any(e in kwargs.keys() for e in ("bytecode","address","sources")):
        raise Exception("invalid request")

    mythril = mythrilCls()
    mythril.set_db_rpc_infura()

    if kwargs.get("bytecode"):
        address, _ = mythril.load_from_bytecode(kwargs.get("bytecode"))
    elif kwargs.get("address"):
        address, _ = mythril.load_from_address(kwargs.get("address"))
    elif kwargs.get("sources"):
        address, _ = mythril.load_from_solidity_sources(kwargs.get("sources"))
    else:
        raise Exception("invalid request")

    return json.loads(mythril.fire_lasers().as_json())


@Request.application
def application(request):

    dispatcher["add"] = lambda a,b:a+b

    response = JSONRPCResponseManager.handle(
        request.get_data(cache=False, as_text=True), dispatcher)
    return Response(response.json, mimetype='application/json')


def serve(cls, bind="localhost", port=4000, as_thread=False):
    global mythrilCls
    mythrilCls = cls
    server_proc = None
    if as_thread:
        server_proc = Thread(target=run_simple, args=(bind, port, application))
        server_proc.daemon = True
        server_proc.start()
    else:
        run_simple(bind, port, application)
    return server_proc

if __name__ == "__main__":
    serve()
