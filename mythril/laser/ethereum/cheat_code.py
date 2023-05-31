import logging
import re
from typing import Union, List, cast, Optional
from eth.constants import GAS_CALLSTIPEND

import mythril.laser.ethereum.util as util
from mythril.laser.ethereum.util import insert_ret_val
from mythril.laser.ethereum import natives
from mythril.laser.ethereum.instruction_data import calculate_native_gas
from mythril.laser.ethereum.state.account import Account
from mythril.laser.ethereum.natives import PRECOMPILE_COUNT, PRECOMPILE_FUNCTIONS
from mythril.laser.ethereum.state.calldata import (
    BaseCalldata,
    SymbolicCalldata,
    ConcreteCalldata,
)
from mythril.laser.ethereum.state.global_state import GlobalState
from mythril.laser.smt import BitVec, If
from mythril.laser.smt import simplify, Expression, symbol_factory
from mythril.support.loader import DynLoader


class hevm_cheat_code:
    # https://github.com/dapphub/ds-test/blob/cd98eff28324bfac652e63a239a60632a761790b/src/test.sol

    address = 0x7109709ECFA91A80626FF3989D68F67F5B1DD12D

    fail_payload = int(
        "70ca10bb"
        + "0000000000000000000000007109709ecfa91a80626ff3989d68f67f5b1dd12d"
        + "6661696c65640000000000000000000000000000000000000000000000000000"
        + "0000000000000000000000000000000000000000000000000000000000000001",
        16,
    )

    assume_sig = 0x4C63E562

    @staticmethod
    def is_cheat_address(address):
        if int(address, 16) == int("0x7109709ECfa91a80626fF3989D68f67F5b1DD12D", 16):
            return True
        if int(address, 16) == int("0x72c68108a82e82617b93d1be0d7975d762035015", 16):
            return True
        return False


def handle_cheat_codes(
    global_state: GlobalState,
    callee_address: Union[str, BitVec],
    call_data: BaseCalldata,
    memory_out_offset: Union[int, Expression],
    memory_out_size: Union[int, Expression],
):

    insert_ret_val(global_state)
    pass
