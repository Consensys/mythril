# Mythril
![Master Build Status](https://img.shields.io/circleci/project/github/ConsenSys/mythril/master.svg)
[![Join the chat at https://gitter.im/ConsenSys/mythril](https://badges.gitter.im/ConsenSys/mythril.svg)](https://gitter.im/ConsenSys/mythril?utm_source=badge&utm_medium=badge&utm_campaign=pr-badge&utm_content=badge)  [![PyPI](https://badge.fury.io/py/mythril.svg)](https://pypi.python.org/pypi/mythril)

<img height="120px" align="right" src="/static/mythril.png"/>

Mythril is a security analysis tool for Ethereum smart contracts. It was introduced in [Smashing Ethereum smart contracts for fun and real profit](https://github.com/b-mueller/smashing-smart-contracts/blob/master/smashing-smart-contracts-1of1.pdf), a conference paper released at [HITBSecConf 2018](https://conference.hitb.org).

  * [Installation and setup](#installation-and-setup)
  * [Security analysis](#security-analysis)
    + [Analyzing Solidity code](#analyzing-solidity-code)
      - [Specifying Solc versions](#specifying-solc-versions)
      - [Output formats](#output-formats)
      - [Analyzing a Truffle project](#analyzing-a-truffle-project)
    + [Analyzing on-chain contracts](#analyzing-on-chain-contracts)
    + [Speed vs. Coverage](#speed-vs-coverage)
  * [Control flow graph](#control-flow-graph)
  * [Blockchain exploration](#blockchain-exploration)
    + [Searching from the command line](#searching-from-the-command-line)
    + [Reading contract storage](#reading-contract-storage)
  * [Utilities](#utilities)
    + [Disassembler](#disassembler)
    + [Calculating function hashes](#calculating-function-hashes)
    + [Function signatures](#function-signatures)
  * [Credit](#credit)

## Installation and setup

Build the [Docker](https://www.docker.com) image:

```bash
$ git clone https://github.com/ConsenSys/mythril/
$ docker build mythril
```

Install from Pypi:

```bash
$ pip3 install mythril
```

If you plan to analyze Solidity code you'll also need the [native version of solc](http://solidity.readthedocs.io/en/v0.4.21/installing-solidity.html#binary-packages). Solcjs is not supported.

## Security analysis

Run `myth -x` with one of the input options described below to run the analysis. This will run the Python modules in the [/analysis/modules](https://github.com/b-mueller/mythril/tree/master/mythril/analysis/modules) directory. 

Mythril detects a range of [security issues](security_checks.md), including integer underflows, owner-overwrite-to-Ether-withdrawal, and others. However, the analysis will not detect business logic issues and is not equivalent to formal verification.

### Analyzing Solidity code

In order to work with Solidity source code files, the [solc command line compiler](http://solidity.readthedocs.io/en/develop/using-the-compiler.html) needs to be installed and in path. You can then provide the source file(s) as positional arguments, e.g.:

```
$ myth -x solidity_examples/ether_send.sol 
==== Ether send ====
Type: Warning
Contract: Crowdfunding
Function name: withdrawfunds()
PC address: 816
In the function `withdrawfunds()` a non-zero amount of Ether is sent to msg.sender.

There is a check on storage index 7. This storage slot can be written to by calling the function `crowdfunding()`.
--------------------
In file: solidity_examples/ether_send.sol:18

msg.sender.transfer(this.balance)

```

If an input file contains multiple contract definitions, Mythril analyzes the *last* bytecode output produced by solc. You can override this by specifying the contract name explicitly:

```
$ myth -x OmiseGo.sol:OMGToken
```

#### Specifying Solc versions

You can specify a version of the solidity compiler to be used with `--solv <version number>`. Please be aware that this uses [py-solc](https://github.com/ethereum/py-solc) and will only work on Linux and OS X versions of Mavericks, Yosemite and El Capitan as of the time of this writing. It will check you locally installed compiler, if this is not what is specified, it will download binaries on Linux or try to compile from source on OS X.

#### Output formats

By default, analysis results are printed to the terminal in text format. You can change the output format with the `-o` argument:

```
$ myth -xo json underflow.sol
```

The `json` format is useful for integration into other tools, while `-o markdown` creates a [human-readable report](static/sample_report.md).

#### Analyzing a Truffle project

[Truffle Suite](http://truffleframework.com) is a popular development framework for Ethereum. To analyze the smart contracts in a Truffle project, change in the project root directory and run `truffle compile` followed by `myth --truffle`.

### Analyzing on-chain contracts

When analyzing contracts on the blockchain, Mythril will by default query a local node via RPC. You can also use the built-in [INFURA](https://infura.io) support. Alternatively, you can override the RPC settings with the `--rpc` argument.

| Argument        | Description     |  
| ------------- |:-------------:| 
| None    | Connect to local Ethereum node |
| `-i`      | Connect to INFURA Mainnet via HTTPS |
| `--rpc ganache` | Connect to local Ganache  | 
| `--rpc infura-[netname]` | Connect to infura-mainnet, rinkeby, kovan or ropsten  | 
| `--rpc HOST:PORT` | Custom RPC connection   Custom |
| `--rpctls <True/False>` | RPC connection over TLS (default: False) | 
| `--ipc` | Connect to local Ethereum node via IPC | 

To analyze a mainnet contract via local RPC:

```
$ myth -xa 0x5c436ff914c458983414019195e0f4ecbef9e6dd
```

Or, using INFURA instead:

```
$ myth -xia 0x5c436ff914c458983414019195e0f4ecbef9e6dd
```

Adding the `-l` flag will cause Mythril to automatically retrieve dependencies, such as dynamically linked library contracts:

```bash
$ myth -xia 0xEbFD99838cb0c132016B9E117563CB41f2B02264 -l -v1
```

### Speed vs. Coverage

The maximum recursion depth for the symbolic execution engine can be controlled with the `--max-depth` argument. The default value is 12. Lowering this value reduces the analysis time as well as the coverage / number of explored states.

```
$ myth -xia 0x5c436ff914c458983414019195e0f4ecbef9e6dd --max-depth 8
```

## Control flow graph

The `-g FILENAME` option generates an [interactive jsViz graph](http://htmlpreview.github.io/?https://github.com/b-mueller/mythril/blob/master/static/mythril.html):

```bash
$ myth -ig ./graph.html -a 0x5c436ff914c458983414019195e0f4ecbef9e6dd --max-depth 8
```

![callgraph](https://raw.githubusercontent.com/b-mueller/mythril/master/static/callgraph8.png "Call graph")

~~The "bounce" effect, while awesome (and thus enabled by default), sometimes messes up the graph layout.~~ Try adding the `--enable-physics` flag for a very entertaining "bounce" effect that unfortunately completely destroys usability.

## Statespace JSON for Traceview Explorer

The `-j FILENAME` option dumps the statespace to json in the format that is required by the [Symbolic Trace Explorer GUI](https://github.com/ConsenSys/mythril-trace-explorer).

```bash
$ ./myth -ij ./statespace.json -a 0x5c436ff914c458983414019195e0f4ecbef9e6dd --max-depth 8
```

## Blockchain exploration

If you are planning to do batch operations or use the contract search features, running a [go-ethereum](https://github.com/ethereum/go-ethereum) node is recommended. Start your local node as follows:

```bash
$ geth --syncmode fast --rpc
```

Mythril builds its own contract database to enable fast search operations. This enables operations like those described in the [legendary "Mitch Brenner" blog post](https://medium.com/@rtaylor30/how-i-snatched-your-153-037-eth-after-a-bad-tinder-date-d1d84422a50b) in ~~seconds~~ minutes instead of days. Unfortunately, the initial sync process is slow. You don't need to sync the whole blockchain right away though: If you abort the syncing process with `ctrl+c`, it will be auto-resumed the next time you run the `--init-db` command.

```bash
$ myth --init-db
Starting synchronization from latest block: 4323706
Processing block 4323000, 3 individual contracts in database
(...)
```

Note that only contracts with non-zero balance are added to the database.

If you experience syncing errors on Mac OS High Sierra, run the following command before starting the sync:

```
export OBJC_DISABLE_INITIALIZE_FORK_SAFETY=YES
```

### Searching from the command line

The search feature allows you to find contract instances that contain specific function calls and opcode sequences. It supports simple boolean expressions, such as:

```bash
$ myth --search "func#changeMultisig(address)#"
$ myth --search "code#PUSH1 0x50,POP#"
$ myth --search "func#changeMultisig(address)# and code#PUSH1 0x50#"
```

### Reading contract storage

You can read the contents of storage slots from a deployed contract as follows.

```bash
$ myth --storage 0,1 -a "0x76799f77587738bfeef09452df215b63d2cfb08a"
0x0000000000000000000000000000000000000000000000000000000000000003
```

## Utilities

### Disassembler

Use the `-d` flag to disassemble code. The disassembler accepts a bytecode string or a contract address as its input.

```bash
$ myth -d -c "0x6060"
0 PUSH1 0x60
```

Specifying an address via `-a ADDRESS` will download the contract code from your node.

```bash
$ myth -d -a "0x2a0c0dbecc7e4d658f48e01e3fa353f44050c208"
0 PUSH1 0x60
2 PUSH1 0x40
4 MSTORE
(...)
1135 - FUNCTION safeAdd(uint256,uint256) -
1136 CALLVALUE
1137 ISZERO
```

### Calculating function hashes

To print the Keccak hash for a given function signature:

```bash
$ myth --hash "setOwner(address)"
0x13af4035
```

### Function signatures

Whenever you disassemble or analyze binary code, Mythril will try to resolve function names using its local signature database. The database must be provided at `~/.mythril/signatures.json`. You can start out with the [default file](signatures.json) as follows:

```
$ mkdir ~/.mythril
$ cd ~/.mythril
$ wget https://raw.githubusercontent.com/b-mueller/mythril/master/signatures.json
```

When you analyze Solidity code, new function signatures are added to the database automatically.


### Use LevelDB directly

If you want to directly use the LevelDB database of your local geth instance you can do so by specifying its path with *--leveldb* option:

```bash
$ myth --leveldb ./geth/chaindata -s "code#PUSH#"
$ myth --leveldb ./geth/chaindata -a 0xA692B965434F804BF7C39217E881F2c229befc2e --storage 0,10
```

Default geth data directories are:

* Mac: `~/Library/Ethereum`
* Linux: `~/.ethereum`
* Windows: `%APPDATA%\Ethereum`

The chaindata LevelDB is located at `<datadir>/geth/chaindata`

## For developers

You can find how to run tests and generate coverage reports in [README_DEV.md](./README_DEV.md)


## Credit

- JSON RPC library is adapted from [ethjsonrpc](https://github.com/ConsenSys/ethjsonrpc) (it doesn't seem to be maintained anymore, and I needed to make some changes to it).

- The signature data in `signatures.json` was initially obtained from the [Ethereum Function Signature Database](https://www.4byte.directory).

- Many features, bugfixes and analysis modules have been added by [contributors](https://github.com/b-mueller/mythril/graphs/contributors).
