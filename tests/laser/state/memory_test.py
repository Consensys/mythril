from z3 import BitVec, simplify

from mythril.laser.ethereum.state.memory import Memory


def test_memory_zeroed():
    # Arrange
    mem = Memory("memory")

    # Act
    mem[11] = 10
    mem.write_word_at(2000, 0x12345)

    # Assert
    assert mem[10] == 0
    assert mem[100] == 0
    assert mem.get_word_at(1000) == 0


def test_memory_write():
    # Arrange
    mem = Memory("memory")
    a = BitVec("a", 256)
    b = BitVec("b", 8)

    # Act
    mem[11] = 10
    mem[12] = b
    mem.write_word_at(200, 0x12345)
    mem.write_word_at(100, a)

    # Assert
    assert mem[0] == 0
    assert mem[11] == 10
    assert mem[200 + 31] == 0x45
    assert mem.get_word_at(200) == 0x12345
    assert simplify(a == mem.get_word_at(100))
    assert simplify(b == mem[12])
