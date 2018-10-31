from mythril.disassembler.disassembly import Disassembly
from mythril.laser.ethereum import svm
from mythril.laser.ethereum.state import Account
import mythril.laser.ethereum.cfg as cfg


def test_intercontract_call():
    # Arrange
    cfg.gbl_next_uid = 0

    caller_code = Disassembly(
        "6080604052348015600f57600080fd5b5073deadbeefdeadbeefdeadbeefdeadbeefdeadbeef73ffffffffffffffffffffffffffffffffffffffff166389627e13336040518263ffffffff167c0100000000000000000000000000000000000000000000000000000000028152600401808273ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff168152602001915050602060405180830381600087803b15801560be57600080fd5b505af115801560d1573d6000803e3d6000fd5b505050506040513d602081101560e657600080fd5b8101908080519060200190929190505050500000a165627a7a72305820fdb1e90f0d9775c94820e516970e0d41380a94624fa963c556145e8fb645d4c90029"
    )
    caller_address = "0xaffeaffeaffeaffeaffeaffeaffeaffeaffeaffe"

    callee_code = Disassembly(
        "608060405260043610603f576000357c0100000000000000000000000000000000000000000000000000000000900463ffffffff16806389627e13146044575b600080fd5b348015604f57600080fd5b506082600480360381019080803573ffffffffffffffffffffffffffffffffffffffff1690602001909291905050506084565b005b8073ffffffffffffffffffffffffffffffffffffffff166108fc3073ffffffffffffffffffffffffffffffffffffffff16319081150290604051600060405180830381858888f1935050505015801560e0573d6000803e3d6000fd5b50505600a165627a7a72305820a6b1335d6f994632bc9a7092d0eaa425de3dea05e015af8a94ad70b3969e117a0029"
    )
    callee_address = "0xdeadbeefdeadbeefdeadbeefdeadbeefdeadbeef"

    caller_account = Account(caller_address, caller_code, contract_name="Caller")
    callee_account = Account(callee_address, callee_code, contract_name="Callee")

    accounts = {caller_address: caller_account, callee_address: callee_account}

    laser = svm.LaserEVM(accounts)

    # Act
    laser.sym_exec(caller_address)

    # Assert
    # Initial node starts in contract caller
    assert len(laser.nodes.keys()) > 0
    assert laser.nodes[0].contract_name == "Caller"

    # At one point we call into contract callee
    for node in laser.nodes.values():
        if node.contract_name == "Callee":
            assert len(node.states[0].transaction_stack) > 1
            return

    assert False
