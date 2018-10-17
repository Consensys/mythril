import pytest
from pysmt.typing import BVType, INT
from pysmt.walkers import IdentityDagWalker
from mythril.laser.ethereum.symbol_manager import \
    SymRedefError, factory, sym_get, sym_set_prop, sym_get_prop


@pytest.fixture
def reset_symbol_manager():
    factory.reset()


def test_sym_get(reset_symbol_manager):
    x = sym_get("x", INT)
    y = sym_get("y", BVType(256))

    x0 = sym_get("x", INT)
    assert (x0 is x)


def test_sym_get_redef_error(reset_symbol_manager):
    x = sym_get("x", INT)
    with pytest.raises(SymRedefError):
        sym_get("x", BVType(256))


def test_set_get_prop(reset_symbol_manager):
    x = sym_get("x", BVType(256))
    sym_set_prop("x", "foo", True)
    assert (sym_get_prop("x", "foo"))


def test_get_prop_nonset(reset_symbol_manager):
    x = sym_get("x", BVType(256))
    with pytest.raises(KeyError):
        sym_get_prop("x", "foo")


def test_simple_taint_analysis(reset_symbol_manager):
    class SimpleTaintWalker(IdentityDagWalker):
        def __init__(self):
            IdentityDagWalker.__init__(self)
            self.tainted = False

        def walk_symbol(self, formula, args, **kwargs):
            name = formula.symbol_name()
            try:
                tainted = sym_get_prop(name, "tainted")
            except KeyError:
                tainted = False
            if tainted:
                self.tainted = True

        def walk_bv_add(self, formula, args, **kwargs):
            return

    x = sym_get("x", BVType(256))
    y = sym_get("y", BVType(256))
    formula = x.get_raw() + y.get_raw()
    sym_set_prop("x", "tainted", True)

    walker = SimpleTaintWalker()
    walker.iter_walk(formula)
    assert (walker.tainted)
