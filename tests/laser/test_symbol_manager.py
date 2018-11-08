import pytest
from mythril.laser.ethereum.symbol_manager import (
    SymRedefError,
    sym_factory,
    sym_get_bv,
    sym_set_prop,
    sym_get_prop,
)


@pytest.fixture
def reset_symbol_manager():
    sym_factory.reset()


def test_sym_get_bv(reset_symbol_manager):
    x = sym_get_bv("x", 256)
    x0 = sym_get_bv("x", 256)
    assert x0 is x


def test_sym_get_bv_redef_error(reset_symbol_manager):
    x = sym_get_bv("x", 256)
    with pytest.raises(SymRedefError):
        sym_get_bv("x", 32)


def test_sym_set_get_prop(reset_symbol_manager):
    x = sym_get_bv("x", 256)
    sym_set_prop("x", "tainted", True)
    assert sym_get_prop("x", "tainted")


def test_sym_get_prop_notset(reset_symbol_manager):
    x = sym_get_bv("x", 256)
    with pytest.raises(KeyError):
        sym_get_prop("x", "tainted")
