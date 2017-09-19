#!/usr/bin/env python
"""mythril.py: Ethereum VM bytecode assembler/ disassembler

   http://www.github.com/b-mueller/mythril
"""

from ether import asm,evm
import sys
import codecs
import argparse
import util


def exitWithError(message):
    print(message)
    sys.exit()


parser = argparse.ArgumentParser(description='Ethereum VM bytecode assembler/ disassembler')

parser.add_argument('-d', '--disassemble',  action='store_true', help='disassemble, use with -c or  --transaction_hash')
parser.add_argument('-a', '--assemble', help='produce bytecode from easm input file', metavar='INPUT FILE')
parser.add_argument('-t', '--trace',  action='store_true', help='trace bytecode provided via the -c argument')
parser.add_argument('-c', '--code', help='bytecode string ("6060604052...")', metavar='BYTECODE')
parser.add_argument('-o', '--outfile')
parser.add_argument('--transaction_hash', help='id of contract creation transaction')
parser.add_argument('--rpchost', default='127.0.0.1', help='RPC host')
parser.add_argument('--rpcport', type=int, default=8545, help='RPC port')

args = parser.parse_args()


if (args.disassemble):

    if (args.code):
        encoded_bytecode = args.code
    elif (args.transaction_hash):

        try:

            encoded_bytecode = util.bytecode_from_blockchain(args.transaction_hash, args.rpchost, args.rpcport)

        except Exception as e:
            exitWithError("Exception loading bytecode via RPC" + str(e.message))

    else:
        exitWithError("Disassembler: Provide the input bytecode via the -c or --transaction_hash arguments")

    disassembly = asm.disassemble(util.safe_decode(encoded_bytecode))

    easm_text = asm.disassembly_to_easm(disassembly)

    if (args.outfile):
        util.string_to_file(args.outfile, easm_text)
    else:
        sys.stdout.write(easm_text)

elif (args.assemble):

    easm = util.file_to_string(args.assemble)

    disassembly = asm.easm_to_disassembly(easm)

    assembly = asm.assemble(disassembly)

    if (args.outfile):
        util.raw_bytes_to_file(args.outfile, assembly)
    else:
        print("0x" + str(codecs.encode(assembly, "hex_codec"), 'ascii'))

elif (args.trace):

    if args.code:     

        evm.trace(util.safe_decode(args.code))

    else:
        exitWithError("Trace: Provide the input bytecode using -c <bytecode>")

else:
    parser.print_help()
