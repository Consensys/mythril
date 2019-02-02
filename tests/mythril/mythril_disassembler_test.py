import pytest
from mythril.mythril import MythrilConfig, MythrilDisassembler
from mythril.exceptions import CriticalError

storage_test = [
    (
        ["438767356", "3"],
        [
            "0x1a270efc: 0x0000000000000000000000000000000000000000000000000000000000000000",
            "0x1a270efd: 0x0000000000000000000000000000000000000000000000000000000000000000",
            "0x1a270efe: 0x0000000000000000000000000000000000000000000000000000000000000000",
        ],
    ),
    (
        ["mapping", "4588934759847", "1", "2"],
        [
            "0x7e523d5aeb10cdb378b0b1f76138c28063a2cb9ec8ff710f42a0972f4d53cf44: "
            "0x0000000000000000000000000000000000000000000000000000000000000000",
            "0xba36da34ceec88853a2ebdde88e023c6919b90348f41e8905b422dc9ce22301c: "
            "0x0000000000000000000000000000000000000000000000000000000000000000",
        ],
    ),
    (
        ["mapping", "4588934759847", "10"],
        [
            "45998575720532480608987132552042185415362901038635143236141343153058112000553: "
            "0x0000000000000000000000000000000000000000000000000000000000000000"
        ],
    ),
    (
        ["4588934759847", "1", "array"],
        [
            "30699902832541380821728647136767910246735388184559883985790189062258823875816: "
            "0x0000000000000000000000000000000000000000000000000000000000000000"
        ],
    ),
]


@pytest.mark.parametrize("params,ans", storage_test)
def test_get_data_from_storage(params, ans):
    config = MythrilConfig()
    config.set_api_rpc_infura()
    disassembler = MythrilDisassembler(eth=config.eth, solc_version="0.4.23")
    outtext = disassembler.get_state_variable_from_storage(
        "0x76799f77587738bfeef09452df215b63d2cfb08a", params
    ).split("\n")
    assert len(outtext) == len(ans)
    for a, b in zip(outtext, ans):
        assert a == b
    assert outtext == ans


storage_test_extra_params = [
    (["1", "2", "3", "4"]),
    (["mapping", "1"]),
    (["a", "b", "c"]),
]


@pytest.mark.parametrize("params", storage_test_extra_params)
def test_get_data_from_storage_extra_params(params):
    config = MythrilConfig()
    config.set_api_rpc_infura()
    disassembler = MythrilDisassembler(eth=config.eth, solc_version="0.4.23")
    with pytest.raises(CriticalError):
        disassembler.get_state_variable_from_storage(
            "0x76799f77587738bfeef09452df215b63d2cfb08a", params
        )
