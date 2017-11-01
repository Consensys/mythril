import unittest
import os
from subprocess import check_output


class CommandLineToolTestCase(unittest.TestCase):

    def runTest(self):

        script_path = os.path.dirname(os.path.realpath(__file__))
        myth = os.path.join(script_path, '..', 'myth')

        out = check_output([myth,'-d','-c', '0x5050']).decode("UTF-8")

        self.assertEqual('0 POP\n1 POP\n', out)

        out = check_output([myth,'-d', os.path.join(script_path,'testdata','metacoin.sol')]).decode("UTF-8")

        self.assertIn('0 PUSH1 0x60\n2 PUSH1 0x40', out)