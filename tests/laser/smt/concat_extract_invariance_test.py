from mythril.laser.smt import Extract, Concat, symbol_factory, BitVecFunc


def test_bitvecfunc_arithmetic():
    input_ = symbol_factory.BitVecSym("input", 256)
    output_ = symbol_factory.BitVecFuncSym(
        "Keccak[input]", size=256, func_name="keccak256", input_=input_
    )
    p1 = Extract(127, 0, output_)
    p2 = Extract(255, 128, output_)
    construct = Concat(p2, p1)
    assert isinstance(construct, BitVecFunc)
    assert construct.input_ == input_


def test_bitvecfunc_arithmetic2():
    input_ = symbol_factory.BitVecSym("input", 256)
    output_ = symbol_factory.BitVecFuncSym(
        "Keccak[input]", size=256, func_name="keccak256", input_=input_
    )
    construct = Concat(output_, symbol_factory.BitVecVal(0, 256))
    assert Extract(511, 256, construct).input_ == input_


def test_bitvecfunc_arithmetic3():
    input_ = symbol_factory.BitVecSym("input", 256)
    output_ = symbol_factory.BitVecFuncSym(
        "Keccak[input]", size=256, func_name="keccak256", input_=input_
    )
    output2_ = symbol_factory.BitVecFuncSym(
        "Keccak[output_]", size=256, func_name="keccak256", input_=output_
    )

    construct = Concat(output2_, symbol_factory.BitVecVal(0, 256))
    assert Extract(511, 256, construct).input_.input_ == input_


def test_bitvecfunc_arithmetic4():
    input_ = symbol_factory.BitVecSym("input", 256)
    output_ = symbol_factory.BitVecFuncSym(
        "Keccak[input]", size=256, func_name="keccak256", input_=input_
    )
    output2_ = symbol_factory.BitVecFuncSym(
        "Keccak[output_]",
        size=256,
        func_name="keccak256",
        input_=Concat(output_, symbol_factory.BitVecVal(0, 256)),
    )

    construct = Concat(output2_, symbol_factory.BitVecVal(0, 256))
    assert Extract(511, 256, Extract(511, 256, construct).input_).input_ == input_
