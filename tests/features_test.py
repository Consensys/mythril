import pytest
from pathlib import Path
from mythril.mythril import MythrilDisassembler
from mythril.solidity.features import SolidityFeatureExtractor
from mythril.solidity.soliditycontract import SolidityContract, SolcAST

TEST_FILES = Path(__file__).parent / "testdata/input_contracts"
solc_binary = MythrilDisassembler._init_solc_binary("v0.5.0")

test_cases = [
    ("suicide.sol", 1, "kill", "contains_selfdestruct", True),
    (
        "SimpleModifier.sol",
        1,
        "withdrawfunds",
        "all_require_vars",
        set(["msg", "owner"]),
    ),
    ("SimpleModifier.sol", 1, "withdrawfunds", "transfer_vars", set(["owner"])),
    ("rubixi.sol", 18, "init", "contains_selfdestruct", False),
    ("rubixi.sol", 18, "collectAllFees", "has_owner_modifier", True),
    ("rubixi.sol", 18, "collectAllFees", "is_payable", False),
    (
        "rubixi.sol",
        18,
        "collectAllFees",
        "all_require_vars",
        set(["collectedFees", "creator"]),
    ),
    (
        "rubixi.sol",
        18,
        "collectPercentOfFees",
        "all_require_vars",
        set(["collectedFees", "_pcent", "creator"]),
    ),
    (
        "rubixi.sol",
        18,
        "changeMultiplier",
        "all_require_vars",
        set(["_mult", "creator"]),
    ),
    ("rubixi.sol", 18, "", "is_payable", True),
    ("rubixi.sol", 18, "collectAllFees", "transfer_vars", set(["creator"])),
    ("exceptions.sol", 8, "assert3", "contains_assert", True),
    ("exceptions.sol", 8, "requireisfine", "all_require_vars", set(["input"])),
    ("WalletLibrary.sol", 23, "execute", "has_owner_modifier", True),
    ("WalletLibrary.sol", 23, "initWallet", "has_owner_modifier", False),
    ("WalletLibrary.sol", 23, "initWallet", "all_require_vars", set(["m_numOwners"])),
    ("WalletLibrary.sol", 23, "confirm", "all_require_vars", set(["success"])),
    ("kcalls.sol", 3, "callSetN", "contains_call", True),
    ("kcalls.sol", 3, "delegatecallSetN", "contains_delegatecall", True),
    ("kcalls.sol", 3, "callcodeSetN", "contains_staticcall", True),
]


@pytest.mark.parametrize(
    "file_name, num_funcs, func_name, field, expected_value", test_cases
)
def test_feature_selfdestruct(file_name, num_funcs, func_name, field, expected_value):
    input_file = TEST_FILES / file_name
    name = file_name.split(".")[0]
    print(name, name.capitalize())
    if name[0].islower():
        name = name.capitalize()
    contract = SolidityContract(str(input_file), name=name, solc_binary=solc_binary)
    ms = contract.solc_json["sources"][str(input_file)]["ast"]
    sfe = SolidityFeatureExtractor(ms)
    fe = sfe.extract_features()
    assert len(fe) == num_funcs
    assert fe[func_name][field] == expected_value
