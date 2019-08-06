import pytest

from configparser import ConfigParser
from pathlib import Path

from mythril.mythril import MythrilConfig
from mythril.exceptions import CriticalError


def test_config_path_dynloading():
    config = MythrilConfig()
    config.config_path = str(
        Path(__file__).parent.parent / "testdata/mythril_config_inputs/config.ini"
    )
    config.set_api_from_config_path()
    assert config.eth.host == "mainnet.infura.io"
    assert config.eth.port == 443


rpc_types_tests = [
    ("infura", "mainnet.infura.io", 443, True),
    ("ganache", "localhost", 7545, True),
    ("infura-rinkeby", "rinkeby.infura.io", 443, True),
    ("infura-ropsten", "ropsten.infura.io", 443, True),
    ("infura-kovan", "kovan.infura.io", 443, True),
    ("localhost", "localhost", 8545, True),
    ("localhost:9022", "localhost", 9022, True),
    ("pinfura", None, None, False),
    ("infura-finkeby", None, None, False),
]


@pytest.mark.parametrize("rpc_type,host,port,success", rpc_types_tests)
def test_set_rpc(rpc_type, host, port, success):
    config = MythrilConfig()
    if success:
        config._set_rpc(rpc_type)
        assert config.eth.host == host
        assert config.eth.port == port
    else:
        with pytest.raises(CriticalError):
            config._set_rpc(rpc_type)


def test_leveldb_config_addition():
    config = ConfigParser()
    config.add_section("defaults")
    MythrilConfig._add_leveldb_option(config, "test")
    assert config.has_section("defaults")
    assert config.get("defaults", "leveldb_dir") == "test"


def test_dynld_config_addition():
    config = ConfigParser()
    config.add_section("defaults")
    MythrilConfig._add_dynamic_loading_option(config)
    assert config.has_section("defaults")
    assert config.get("defaults", "dynamic_loading") == "infura"
