from pysmt.shortcuts import reset_env, get_env, Symbol
from pysmt.typing import BVType


def test_bv_prop():
    reset_env()
    get_env().enable_infix_notation = True

    # Check if a modified pySMT which supports attaching arbitrary
    # properties to pySMT FNode is used.

    x = Symbol("x", BVType(256))
    x.set_prop("tainted", True)
    assert (x.get_prop("tainted") == True)

    y = x + x
    if x.get_prop("tainted"):
        y.set_prop("tainted", True)
    assert (y.get_prop("tainted") == True)
