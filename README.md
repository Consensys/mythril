# Mythril

Mythril is an assembler and disassembler for Ethereum VM bytecode. It was created for low-level testing/fuzzing of EVM implementations.

## Installation

Clone the git repo:

```bash
$ git clone https://github.com/b-mueller/mythril/
$ pip install -r requirements.txt
```

## Usage

To disassemble a piece of bytecode, pass it on the command line:

```bash
$ ./mythril.py -d -c "0x606060405050"
PUSH1 0x60
PUSH1 0x40
POP
POP
```

### Modifying and re-assembling code

Mythril can assemble code from input files that contain one instruction per line. To start from an existing contract, save the disassembly to a text file:

```bash
$ ./mythril.py -d -c "0x606060405050" -o code.easm
```

Edit the instructions in a text editor. For example, we can modify the `PUSH` instructions from the original example:

```
PUSH2 0x4050
PUSH4 0x60708090
POP
POP
```

Save the file and run Mythril with the `-a` flag to re-assemble:

```
$ ./mythril.py -a code.easm 
0x61405063607080905050
```

The virtual machine language is described in the [Ethereum Yellowpaper](http://gavwood.com/paper.pdf).

### Tracing EVM execution

You can run a piece of bytecode in the [PyEthereum](https://github.com/ethereum/pyethereum) VM and trace its execution using the `-t` flag. This will output the instructions executed as well as the state of the stack for every execution step. To run code from the command line, use:

```bash
$ ./mythril.py -t -c "0x606060405050"
vm stack=[] op=PUSH1 steps=0 pc=b'0' address=b'\x01#Eg\x89\xab\xcd\xef\x01#Eg\x89\xab\xcd\xef\x01#Eg' depth=0 pushvalue=96 gas=b'1000000' storage={'code': '0x', 'nonce': '0', 'balance': '0', 'storage': {}} inst=96
vm stack=[b'96'] op=PUSH1 steps=1 depth=0 pushvalue=64 gas=b'999997' pc=b'2' inst=96
vm stack=[b'96', b'64'] op=POP steps=2 depth=0 gas=b'999994' pc=b'4' inst=80
vm stack=[b'96'] op=POP steps=3 depth=0 gas=b'999992' pc=b'5' inst=80
```

For larger contracts, you might prefer to compile them to a binary file instead:

```
$ ./mythril.py -a contract.easm -o contract.bin
$ ./mythril.py --trace -f contract.bin
```

### Disassembling a contract from the Ethereum blockchain

You can also load code from an existing contract in the Ethereum blockchain. For this, you need to have a full node running, and the RPC debug interface must be activated. For example, when running `geth` you can do this as follows:

```bash
$ geth --syncmode full --rpc --rpcapi eth,debug
```

To load contract code from your node, pass the TxID of the transaction that created the contract:

```bash
$ ./mythril.py -d --txid 0x23112645da9ae684270de843faaeb44918c79a09e019d3a6cf8b87041020340e -o some_contract.easm
```

Note: If you want to get code from the Ethereum mainnet, it is easier to download it from [Etherscan](https://etherscan.io).
