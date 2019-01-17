from mythril.disassembler.disassembly import *

instruction_list = [
    {"opcode": "PUSH4", "argument": "0x10203040"},
    {"opcode": "EQ"},
    {"opcode": "PUSH4", "argument": "0x40302010"},
    {"opcode": "JUMPI"},
]


def test_get_function_info(mocker):
    # Arrange
    global instruction_list

    signature_database_mock = SignatureDB()
    mocker.patch.object(signature_database_mock, "get")
    signature_database_mock.get.return_value = ["function_name"]

    # Act
    function_hash, entry_point, function_name = get_function_info(
        0, instruction_list, signature_database_mock
    )

    # Assert
    assert function_hash == "0x10203040"
    assert entry_point == 0x40302010
    assert function_name == "function_name"


def test_get_function_info_multiple_names(mocker):
    # Arrange
    global instruction_list

    signature_database_mock = SignatureDB()
    mocker.patch.object(signature_database_mock, "get")
    signature_database_mock.get.return_value = ["function_name", "another_name"]

    # Act
    function_hash, entry_point, function_name = get_function_info(
        0, instruction_list, signature_database_mock
    )

    # Assert
    assert function_name == "**ambiguous** function_name"


def test_get_function_info_no_names(mocker):
    # Arrange
    global instruction_list

    signature_database_mock = SignatureDB()
    mocker.patch.object(signature_database_mock, "get")
    signature_database_mock.get.return_value = []

    # Act
    function_hash, entry_point, function_name = get_function_info(
        0, instruction_list, signature_database_mock
    )

    # Assert
    assert function_name == "_function_0x10203040"
