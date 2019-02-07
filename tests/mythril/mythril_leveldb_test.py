import io
import pytest
from contextlib import redirect_stdout
from pathlib import Path

from mythril.mythril import MythrilLevelDB, MythrilConfig
from mythril.exceptions import CriticalError

config = MythrilConfig()
config.set_api_leveldb(str(Path(__file__).parent / "../leveldb_dir/geth/chaindata"))


def test_leveldb_code_search():
    leveldb_search = MythrilLevelDB(leveldb=config.eth_db)
    f = io.StringIO()
    with redirect_stdout(f):
        leveldb_search.search_db("code#PUSH#")
    out = f.getvalue()
    assert len(out.split("\n")) == 67
    assert "0xddbb615cb2ffaff7233d8a6f3601621de94795e1" in out


def test_leveldb_hash_search_incorrect_input():
    leveldb_search = MythrilLevelDB(leveldb=config.eth_db)
    with pytest.raises(CriticalError):
        leveldb_search.contract_hash_to_address("0x23")


def test_leveldb_hash_search_correct_input():
    leveldb_search = MythrilLevelDB(leveldb=config.eth_db)
    f = io.StringIO()
    with redirect_stdout(f):
        leveldb_search.contract_hash_to_address(
            "0x0464e651bcc40de28fc7fcde269218d16850bac9689da5f4a6bd640fd3cdf6aa"
        )
    out = f.getvalue()
    assert out == "0xddbb615cb2ffaff7233d8a6f3601621de94795e1\n"
