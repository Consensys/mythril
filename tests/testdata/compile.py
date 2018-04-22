# compile test contracts
from pathlib import Path
from mythril.ether.soliditycontract import SolidityContract

# Recompiles all the to be tested contracts
root = Path(__file__).parent
input = root / 'input_contracts'
output = root / 'inputs'

for contract in input.iterdir():
    sol = SolidityContract(str(contract))
    code = sol.code

    output_file = (output / "{}.o".format(contract.name))
    output_file.write_text(code)
