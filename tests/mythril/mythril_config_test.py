import pytest
import os

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
    assert "mainnet.infura.io/v3/blah" == config.eth.host


rpc_types_tests = [
    ("infura", "mainnet.infura.io/v3/blah", None, True),
    ("ganache", "localhost", None, True),
    ("infura-rinkeby", "rinkeby.infura.io/v3/blah", None, True),
    ("infura-ropsten", "ropsten.infura.io/v3/blah", None, True),
    ("infura-kovan", "kovan.infura.io/v3/blah", None, True),
    ("localhost", "localhost", 8545, True),
    ("localhost:9022", "localhost", 9022, True),
    ("pinfura", None, None, False),
    ("infura-finkeby", None, None, False),
]
os.environ["INFURA_ID"] = "blah"


@pytest.mark.parametrize("rpc_type,host,port,success", rpc_types_tests)
def test_set_rpc(rpc_type, host, port, success):
    config = MythrilConfig()
    if success:
        config._set_rpc(rpc_type)
        assert host == config.eth.host
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
