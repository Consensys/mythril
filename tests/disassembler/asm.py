from mythril.disassembler.asm import *
import pytest

valid_names = [("PUSH1", 0x60), ("STOP", 0x0), ("RETURN", 0xf3)]


@pytest.mark.parametrize("operation_name, hex_value", valid_names)
def test_get_opcode(operation_name: str, hex_value: int):
    # Act
    return_value = get_opcode_from_name(operation_name)
    # Assert
    assert return_value == hex_value


def test_get_unknown_opcode():
    operation_name = "definitely unknown"

    # Act
    with pytest.raises(RuntimeError):
        get_opcode_from_name(operation_name)
