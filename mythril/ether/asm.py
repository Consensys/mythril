import sys
import re
from ethereum import opcodes
from mythril.ether import util


regex_PUSH = re.compile('^PUSH(\d*)$')


def instruction_list_to_easm(instruction_list):
    easm = ""

    # print(instruction_list)

    for instruction in instruction_list:

        easm += str(instruction['address']) + " " + instruction['opcode']

        if 'argument' in instruction:
            easm += " " + instruction['argument']

        easm += "\n"

    return easm


def easm_to_instruction_list(easm):

    regex_CODELINE = re.compile('^([A-Z0-9]+)(?:\s+([0-9a-fA-Fx]+))?$')

    instruction_list = []

    codelines = easm.split('\n')

    for line in codelines:

        m = re.search(regex_CODELINE, line)

        if not m:
            # Invalid code line
            continue

        instruction = {}

        instruction['opcode'] = m.group(1)

        if m.group(2):
            instruction['argument'] = m.group(2)[2:]

        instruction_list.append(instruction)

    return instruction_list


def get_opcode_from_name(name):

    for opcode, value in opcodes.opcodes.items():

        if name == value[0]:

            return opcode

    raise RuntimeError("Unknown opcode")


def find_opcode_sequence(pattern, instruction_list):
    match_indexes = []

    pattern_length = len(pattern)

    for i in range(0, len(instruction_list) - pattern_length + 1):

        if instruction_list[i]['opcode'] == pattern[0]:

            matched = True

            for j in range(1, len(pattern)):

                if not (instruction_list[i + j]['opcode'] == pattern[j]):
                    matched = False
                    break

            if (matched):
                match_indexes.append(i)

    return match_indexes


def disassemble(bytecode):

    instruction_list = []
    addr = 0

    while addr < len(bytecode):

        instruction = {}

        instruction['address'] = addr

        try:
            if (sys.version_info > (3, 0)):
                opcode = opcodes.opcodes[bytecode[addr]]
            else:
                opcode = opcodes.opcodes[ord(bytecode[addr])]

        except KeyError:

            # invalid opcode
            instruction_list.append({'address': addr, 'opcode': "INVALID"})
            addr += 1
            continue

        instruction['opcode'] = opcode[0]

        m = re.search(regex_PUSH, opcode[0])

        if m:
            argument = bytecode[addr+1:addr+1+int(m.group(1))]
            instruction['argument'] = "0x" + argument.encode("hex")
            addr += int(m.group(1))

        instruction_list.append(instruction)

        addr += 1

    return instruction_list


def assemble(instruction_list):

    bytecode = b""

    for instruction in instruction_list:

        try:
            opcode = get_opcode_from_name(instruction['opcode'])
        except RuntimeError:
            opcode = 0xbb

        bytecode += opcode.to_bytes(1, byteorder='big')

        if 'argument' in instruction:

            bytecode += util.safe_decode(instruction['argument'])

    return bytecode
