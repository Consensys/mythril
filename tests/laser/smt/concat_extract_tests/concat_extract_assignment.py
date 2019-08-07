from mythril.laser.smt import Extract, Concat, symbol_factory


def test_concat_extract_assignment():
    inp1 = symbol_factory.BitVecSym("input1", 256)
    inp2 = symbol_factory.BitVecSym("input2", 256)
    output1 = symbol_factory.BitVecFuncSym(
        "Keccak[input]", size=256, func_name="keccak256", input_=Concat(inp1, inp2)
    )
    output = Concat(output1, symbol_factory.BitVecVal(0, 256))
    Extract(511, 256, output).potential_inputs = [inp2, inp2]
    assert Extract(511, 256, output).potential_inputs == [inp2, inp2]


def test_concat_extract_assignment_nested():
    inp1 = symbol_factory.BitVecSym("input1", 256)
    o1 = symbol_factory.BitVecFuncSym(
        "Keccak[inp1]",
        size=256,
        func_name="keccak256",
        input_=Concat(inp1, symbol_factory.BitVecVal(0, 256)),
    )
    output1 = symbol_factory.BitVecFuncSym(
        "Keccak[input]",
        size=256,
        func_name="keccak256",
        input_=Concat(o1, symbol_factory.BitVecVal(0, 256)),
    )
    output = Concat(output1, symbol_factory.BitVecVal(0, 256))
    Extract(511, 256, Extract(511, 256, output1.input_).input_).potential_inputs = [
        inp1,
        inp1,
    ]
    assert Extract(
        511, 256, Extract(511, 256, output1.input_).input_
    ).potential_inputs == [inp1, inp1]
