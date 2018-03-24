from unittest import TestCase

from mythril.ether import asm, util

class AsmTestCase(TestCase):

    def test_disassemble(self):
        code = util.safe_decode("0x6060")
        instruction_list = asm.disassemble(code)
        self.assertEqual(instruction_list, [{'address': 0, 'opcode': 'PUSH1', 'argument': '0x60'}])
