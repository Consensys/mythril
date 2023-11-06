import pytest
from pathlib import Path
from mythril.mythril import MythrilDisassembler
from mythril.solidity.features import SolidityFeatureExtractor
from mythril.solidity.soliditycontract import SolidityContract, SolcAST

TEST_FILES = Path(__file__).parent / "testdata/input_contracts"
solc_binary_5 = MythrilDisassembler._init_solc_binary("v0.5.0")
solc_binary_8 = MythrilDisassembler._init_solc_binary("v0.8.0")
solc_binary_82 = MythrilDisassembler._init_solc_binary("v0.8.20")


test_cases = [
    ("suicide.sol", 1, "kill", "contains_selfdestruct", True, solc_binary_5),
    (
        "SimpleModifier.sol",
        1,
        "withdrawfunds",
        "all_require_vars",
        set(["msg", "owner"]),
        solc_binary_5,
    ),
    (
        "SimpleModifier.sol",
        1,
        "withdrawfunds",
        "transfer_vars",
        set(["owner"]),
        solc_binary_5,
    ),
    ("rubixi.sol", 18, "init", "contains_selfdestruct", False, solc_binary_5),
    ("rubixi.sol", 18, "collectAllFees", "has_owner_modifier", True, solc_binary_5),
    ("rubixi.sol", 18, "collectAllFees", "is_payable", False, solc_binary_5),
    (
        "rubixi.sol",
        18,
        "collectAllFees",
        "all_require_vars",
        set(["collectedFees", "creator"]),
        solc_binary_5,
    ),
    (
        "rubixi.sol",
        18,
        "collectPercentOfFees",
        "all_require_vars",
        set(["collectedFees", "_pcent", "creator"]),
        solc_binary_5,
    ),
    (
        "rubixi.sol",
        18,
        "changeMultiplier",
        "all_require_vars",
        set(["_mult", "creator"]),
        solc_binary_5,
    ),
    ("rubixi.sol", 18, "", "is_payable", True, solc_binary_5),
    (
        "rubixi.sol",
        18,
        "collectAllFees",
        "transfer_vars",
        set(["creator"]),
        solc_binary_5,
    ),
    ("exceptions.sol", 8, "assert3", "contains_assert", True, solc_binary_5),
    (
        "exceptions.sol",
        8,
        "requireisfine",
        "all_require_vars",
        set(["input"]),
        solc_binary_5,
    ),
    ("WalletLibrary.sol", 23, "execute", "has_owner_modifier", True, solc_binary_5),
    ("WalletLibrary.sol", 23, "initWallet", "has_owner_modifier", False, solc_binary_5),
    (
        "WalletLibrary.sol",
        23,
        "initWallet",
        "all_require_vars",
        set(["m_numOwners"]),
        solc_binary_5,
    ),
    (
        "WalletLibrary.sol",
        23,
        "confirm",
        "all_require_vars",
        set(["success"]),
        solc_binary_5,
    ),
    ("kcalls.sol", 3, "callSetN", "contains_call", True, solc_binary_5),
    ("kcalls.sol", 3, "delegatecallSetN", "contains_delegatecall", True, solc_binary_5),
    ("kcalls.sol", 3, "callcodeSetN", "contains_staticcall", True, solc_binary_5),
    (
        "regression_1.sol",
        5,
        "transfer",
        "all_require_vars",
        set(["userBalances", "msg", "_to", "_amount"]),
        solc_binary_8,
    ),
    ("SecureVault.sol", 11, "withdraw", "has_owner_modifier", True, solc_binary_82),
    ("SecureVault.sol", 11, "deposit", "has_owner_modifier", False, solc_binary_82),
    (
        "SecureVault.sol",
        11,
        "withdraw",
        "all_require_vars",
        set(["amount", "this"]),
        solc_binary_82,
    ),
]


@pytest.mark.parametrize(
    "file_name, num_funcs, func_name, field, expected_value, solc_binary", test_cases
)
def test_features(file_name, num_funcs, func_name, field, expected_value, solc_binary):
    input_file = TEST_FILES / file_name
    name = file_name.split(".")[0]
    if name[0].islower():
        name = name.capitalize()
    contract = SolidityContract(str(input_file), name=name, solc_binary=solc_binary)
    ms = contract.solc_json["sources"][str(input_file)]["ast"]
    sfe = SolidityFeatureExtractor(ms)
    fe = sfe.extract_features()
    assert len(fe) == num_funcs
    assert fe[func_name][field] == expected_value
