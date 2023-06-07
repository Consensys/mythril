from mythril.disassembler.asm import *
import pytest

valid_names = [("PUSH1", 0x60), ("STOP", 0x0), ("RETURN", 0xF3)]


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


sequence_match_test_data = [
    # Normal no match
    (
        (["PUSH1"], ["EQ"]),
        [{"opcode": "PUSH1"}, {"opcode": "PUSH3"}, {"opcode": "EQ"}],
        1,
        False,
    ),
    # Normal match
    (
        (["PUSH1"], ["EQ"]),
        [{"opcode": "PUSH1"}, {"opcode": "PUSH1"}, {"opcode": "EQ"}],
        1,
        True,
    ),
    # Out of bounds pattern
    (
        (["PUSH1"], ["EQ"]),
        [{"opcode": "PUSH1"}, {"opcode": "PUSH3"}, {"opcode": "EQ"}],
        3,
        False,
    ),
    (
        (["PUSH1"], ["EQ"]),
        [{"opcode": "PUSH1"}, {"opcode": "PUSH3"}, {"opcode": "EQ"}],
        2,
        False,
    ),
    # Double option match
    (
        (["PUSH1", "PUSH3"], ["EQ"]),
        [{"opcode": "PUSH1"}, {"opcode": "PUSH1"}, {"opcode": "EQ"}],
        1,
        True,
    ),
    (
        (["PUSH1", "PUSH3"], ["EQ"]),
        [{"opcode": "PUSH1"}, {"opcode": "PUSH3"}, {"opcode": "EQ"}],
        1,
        True,
    ),
    # Double option no match
    (
        (["PUSH1", "PUSH3"], ["EQ"]),
        [{"opcode": "PUSH1"}, {"opcode": "PUSH3"}, {"opcode": "EQ"}],
        0,
        False,
    ),
]


@pytest.mark.parametrize(
    "pattern, instruction_list, index,  expected_result", sequence_match_test_data
)
def test_is_sequence_match(pattern, instruction_list, index, expected_result):
    # Act
    return_value = is_sequence_match(pattern, instruction_list, index)
    # Assert
    assert return_value == expected_result


find_sequence_match_test_data = [
    # Normal no match
    (
        (["PUSH1"], ["EQ"]),
        [{"opcode": "PUSH1"}, {"opcode": "PUSH3"}, {"opcode": "EQ"}],
        [],
    ),
    # Normal match
    (
        (["PUSH1"], ["EQ"]),
        [
            {"opcode": "PUSH1"},
            {"opcode": "PUSH1"},
            {"opcode": "EQ"},
            {"opcode": "PUSH1"},
            {"opcode": "EQ"},
        ],
        [1, 3],
    ),
]


@pytest.mark.parametrize(
    "pattern, instruction_list, expected_result", find_sequence_match_test_data
)
def test_find_op_code_sequence(pattern, instruction_list, expected_result):
    # Act
    return_value = list(find_op_code_sequence(pattern, instruction_list))

    # Assert
    assert return_value == expected_result


def test_disassemble():
    # Act
    instruction_list = disassemble(b"\x00\x16\x06")

    # Assert
    assert instruction_list[0]["opcode"] == "STOP"
    assert instruction_list[1]["opcode"] == "AND"
    assert instruction_list[2]["opcode"] == "MOD"
