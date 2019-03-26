import io
import pytest
from contextlib import redirect_stdout
from mock import patch

from mythril.mythril import MythrilLevelDB, MythrilConfig
from mythril.exceptions import CriticalError


@patch("mythril.ethereum.interface.leveldb.client.EthLevelDB.search")
@patch("mythril.ethereum.interface.leveldb.client.ETH_DB", return_value=None)
@patch("mythril.ethereum.interface.leveldb.client.LevelDBReader", return_value=None)
@patch("mythril.ethereum.interface.leveldb.client.LevelDBWriter", return_value=None)
def test_leveldb_code_search(mock_leveldb, f1, f2, f3):
    config = MythrilConfig()
    config.set_api_leveldb("some path")
    leveldb_search = MythrilLevelDB(leveldb=config.eth_db)
    leveldb_search.search_db("code#PUSH#")
    mock_leveldb.assert_called()


@patch("mythril.ethereum.interface.leveldb.client.ETH_DB", return_value=None)
@patch("mythril.ethereum.interface.leveldb.client.LevelDBReader", return_value=None)
@patch("mythril.ethereum.interface.leveldb.client.LevelDBWriter", return_value=None)
def test_leveldb_hash_search_incorrect_input(f1, f2, f3):
    config = MythrilConfig()
    config.set_api_leveldb("some path")
    leveldb_search = MythrilLevelDB(leveldb=config.eth_db)
    with pytest.raises(CriticalError):
        leveldb_search.contract_hash_to_address("0x23")


@patch(
    "mythril.ethereum.interface.leveldb.client.EthLevelDB.contract_hash_to_address",
    return_value="0xddbb615cb2ffaff7233d8a6f3601621de94795e1",
)
@patch("mythril.ethereum.interface.leveldb.client.ETH_DB", return_value=None)
@patch("mythril.ethereum.interface.leveldb.client.LevelDBReader", return_value=None)
@patch("mythril.ethereum.interface.leveldb.client.LevelDBWriter", return_value=None)
def test_leveldb_hash_search_correct_input(mock_hash_to_address, f1, f2, f3):
    config = MythrilConfig()
    config.set_api_leveldb("some path")
    leveldb_search = MythrilLevelDB(leveldb=config.eth_db)
    f = io.StringIO()
    with redirect_stdout(f):
        leveldb_search.contract_hash_to_address(
            "0x0464e651bcc40de28fc7fcde269218d16850bac9689da5f4a6bd640fd3cdf6aa"
        )
    out = f.getvalue()
    mock_hash_to_address.assert_called()
    assert out == "0xddbb615cb2ffaff7233d8a6f3601621de94795e1\n"
