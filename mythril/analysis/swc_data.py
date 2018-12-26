DEFAULT_FUNCTION_VISIBILITY = "100"
INTEGER_OVERFLOW_AND_UNDERFLOW = "101"
OUTDATED_COMPILER_VERSION = "102"
FLOATING_PRAGMA = "103"
UNCHECKED_RET_VAL = "104"
UNPROTECTED_ETHER_WITHDRAWAL = "105"
UNPROTECTED_SELFDESTRUCT = "106"
REENTRANCY = "107"
DEFAULT_STATE_VARIABLE_VISIBILITY = "108"
UNINITIALIZED_STORAGE_POINTER = "109"
ASSERT_VIOLATION = "110"
DEPRICATED_FUNCTIONS_USAGE = "111"
DELEGATECALL_TO_UNTRUSTED_CONTRACT = "112"
MULTIPLE_SENDS = "113"
TX_ORDER_DEPENDENCE = "114"
TX_ORIGIN_USAGE = "115"
TIMESTAMP_DEPENDENCE = "116"
INCORRECT_CONSTRUCTOR_NAME = "118"
SHADOWING_STATE_VARIABLES = "119"
WEAK_RANDOMNESS = "120"
SIGNATURE_REPLAY = "121"
IMPROPER_VERIFICATION_BASED_ON_MSG_SENDER = "122"

PREDICTABLE_VARS_DEPENDENCE = (
    "N/A"
)  # TODO: Add the swc id when this is added to the SWC Registry

SWC_TO_TITLE = {
    "100": "Function Default Visibility",
    "101": "Integer Overflow and Underflow",
    "102": "Outdated Compiler Version",
    "103": "Floating Pragma",
    "104": "Unchecked Call Return Value",
    "105": "Unprotected Ether Withdrawal",
    "106": "Unprotected SELFDESTRUCT Instruction",
    "107": "Reentrancy",
    "108": "State Variable Default Visibility",
    "109": "Uninitialized Storage Pointer",
    "110": "Assert Violation",
    "111": "Use of Deprecated Solidity Functions",
    "112": "Delegatecall to Untrusted Callee",
    "113": "DoS with Failed Call",
    "114": "Transaction Order Dependence",
    "115": "Authorization through tx.origin",
    "116": "Timestamp Dependence",
    "117": "Signature Malleability",
    "118": "Incorrect Constructor Name",
    "119": "Shadowing State Variables",
    "120": "Weak Sources of Randomness from Chain Attributes",
    "121": "Missing Protection against Signature Replay Attacks",
    "122": "Lack of Proper Signature Verification",
}
