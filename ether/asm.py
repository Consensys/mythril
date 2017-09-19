import sys
import re
import codecs
from ethereum import opcodes


regex_PUSH = re.compile('^PUSH(\d*)$')


def disassembly_to_easm(disassembly):
    easm = ""

    for instruction in disassembly:
        easm += instruction['opcode']

        if 'argument' in instruction:
            easm += " 0x" + codecs.decode(instruction['argument'], 'ascii')

        easm += "\n"

    return easm


def easm_to_disassembly(easm):

    regex_CODELINE = re.compile('^([A-Z0-9]+)(?:\s+([0-9a-fA-Fx]+))?$')

    disassembly = []

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

        disassembly.append(instruction)

    return disassembly


def get_opcode_from_name(name):

    for opcode, value in opcodes.opcodes.items():

        if name == value[0]:

            return opcode

    raise RuntimeError("Unknown opcode")


def find_opcode_sequence(pattern, disassembly):
    match_indexes = []

    pattern_length = len(pattern)

    for i in range(0, len(disassembly) - pattern_length):

        if disassembly[i]['opcode'] == pattern[0]:

            matched = True

            for j in range(1, len(pattern)):

                if not (disassembly[i + j]['opcode'] == pattern[j]):
                    matched = False
                    break

            if (matched):
                match_indexes.append(i)

    return match_indexes


def resolve_functions(disassembly):

    function_stubs = find_opcode_sequence(['PUSH4', 'EQ', 'PUSH2', 'JUMPI'], disassembly)

    functions = []

    for index in function_stubs:
        func = {}

        func['hash'] = disassembly[index]['argument']
        func['address'] = disassembly[index + 2]['argument']

        functions.append(func)

    return functions


def disassemble(bytecode):

    disassembly = []
    i = 0

    while i < len(bytecode):

        instruction = {}

        try:
            if (sys.version_info > (3, 0)):
                opcode = opcodes.opcodes[bytecode[i]]
            else:
                 opcode = opcodes.opcodes[ord(bytecode[i])]

        except KeyError:

            # invalid opcode
            disassembly.append({'opcode': "INVALID"})
            i += 1
            continue

        instruction['opcode'] = opcode[0]

        m = re.search(regex_PUSH, opcode[0])

        if m:
            argument = bytecode[i+1:i+1+int(m.group(1))]
            instruction['argument'] = codecs.encode(argument, "hex_codec")
            i += int(m.group(1))

        disassembly.append(instruction)

        i += 1

    return disassembly


def assemble(disassembly):

    bytecode = b""

    for instruction in disassembly:

        try:
            opcode = get_opcode_from_name(instruction['opcode'])
        except RuntimeError:
            opcode = 0xbb

        bytecode += opcode.to_bytes(1, byteorder='big')

        if 'argument' in instruction:

            bytecode += bytes(instruction['argument'], 'ascii')

    return bytecode
