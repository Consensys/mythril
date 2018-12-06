from typing import Union
from z3 import BitVecRef, Extract, BitVecVal, If, BoolRef, Z3Exception, simplify, Concat

from mythril.laser.ethereum import util


class Memory:
    def __init__(self):
        self._memory = []

    def __len__(self):
        return len(self._memory)

    def extend(self, size):
        self._memory.extend(bytearray(size))

    def get_word_at(self, index: int) -> Union[int, BitVecRef]:
        """
        Access a word from a specified memory index
        :param index: integer representing the index to access
        :return: 32 byte word at the specified index
        """
        try:
            return util.concrete_int_from_bytes(
                bytes([util.get_concrete_int(b) for b in self[index : index + 32]]), 0
            )
        except TypeError:
            return simplify(
                Concat(
                    [
                        b if isinstance(b, BitVecRef) else BitVecVal(b, 256)
                        for b in self[index : index + 32]
                    ]
                )
            )

    def write_word_at(
        self, index: int, value: Union[int, BitVecRef, bool, BoolRef]
    ) -> None:
        """
        Writes a 32 byte word to memory at the specified index`
        :param index: index to write to
        :param value: the value to write to memory
        """
        try:
            # Attempt to concretize value
            if isinstance(value, bool):
                _bytes = (
                    int(1).to_bytes(32, byteorder="big")
                    if value
                    else int(0).to_bytes(32, byteorder="big")
                )
            else:
                _bytes = util.concrete_int_to_bytes(value)
            assert len(_bytes) == 32
            self[index : index + 32] = _bytes
        except (Z3Exception, AttributeError):  # BitVector or BoolRef
            if isinstance(value, BoolRef):
                value_to_write = If(value, BitVecVal(1, 256), BitVecVal(0, 256))
            else:
                value_to_write = value
            assert value_to_write.size() == 256

            for i in range(0, value_to_write.size(), 8):
                self[index + 31 - (i // 8)] = Extract(i + 7, i, value_to_write)

    def __getitem__(self, item: Union[int, slice]) -> Union[BitVecRef, int, list]:
        if isinstance(item, slice):
            start, step, stop = item.start, item.step, item.stop
            if start is None:
                start = 0
            if stop is None:  # 2**256 is just a bit too big
                raise IndexError("Invalid Memory Slice")
            if step is None:
                step = 1
            return [self[i] for i in range(start, stop, step)]

        try:
            return self._memory[item]
        except IndexError:
            return 0

    def __setitem__(self, key: Union[int, slice], value: Union[BitVecRef, int, list]):
        if isinstance(key, slice):
            start, step, stop = key.start, key.step, key.stop

            if start is None:
                start = 0
            if stop is None:
                raise IndexError("Invalid Memory Slice")
            if step is None:
                step = 1

            for i in range(0, stop - start, step):
                self[start + i] = value[i]

        else:
            if isinstance(value, int):
                assert 0 <= value <= 0xFF
            if isinstance(value, BitVecRef):
                assert value.size() == 8
            self._memory[key] = value
