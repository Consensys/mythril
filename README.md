# Mythril

<img height="60px" align="right" src="/static/mythril.png"/>

Mythril is a reverse engineering and bug hunting framework for the Ethereum blockchain.

## Be responsible!

The purpose of project is to aid discovery of vulnerable smart contracts on the Ethereum mainnet and support research for novel security flaws. If you do find an exploitable issue or vulnerable contract instances, please [do the right thing](https://en.wikipedia.org/wiki/Responsible_disclosure). Also, note that vulnerability branding ("etherbleed", "chainshock",...) is highly discouraged as it will annoy the author and others in the security community.

## Installation and setup

Install from Pypi:

```bash
$ pip install mythril==0.2.8
```

Or, clone the GitHub repo to install the newest master branch:

```bash
$ git clone https://github.com/b-mueller/mythril/
$ cd mythril
$ python setup.py install
```

You also need a [go-ethereum](https://github.com/ethereum/go-ethereum) node that is synced with the network (not that Mythril uses non-standard RPC APIs offered by go-ethereum, so other clients likely won't work). Start the node as follows:

```bash
$ geth --rpc --rpcapi eth,admin,debug --syncmode fast
```

### Database initialization

Mythril builds its own contract database using RPC sync. Unfortunately, this process is slow - however, you don't need to sync the whole blockchain right away. If you abort the syncing process with `ctrl+c`, it will auto-resume the next time you run the `--init-db` command.

```bash
$ mythril --init-db
Starting synchronization from latest block: 4323706
Processing block 4323000, 3 individual contracts in database
(...)
```

The default behavior is to only sync contracts with a non-zero balance. You can disable this behavior with the `--sync-all` flag, but note that this will result in a very large (multi-gigabyte) database.

## Command line usage

The `mythril` command line tool allows you to easily access most of Mythril's functionality.

### Searching the database

The search feature allows you to find contract instances that contain specific function calls and opcode sequences. It supports simple boolean expressions, such as:

```bash
$ mythril --search "func#changeMultisig(address)#"
$ mythril --search "code#PUSH1 0x50,POP#"
$ mythril --search "func#changeMultisig(address)# and code#PUSH1 0x50#"
```

### Disassembler

You can also disassemble and trace code using the `-d` and `-t` flags, respectively. When tracing, the code is run in the PyEthereum virtual machine with the (optional) input data passed via the `--data` flag.

```
$ mythril -d -a "0x3665f2bf19ee5e207645f3e635bf0f4961d661c0"
PUSH1 0x60
PUSH1 0x40
(...)
$ mythril -t -a "0x3665f2bf19ee5e207645f3e635bf0f4961d661c0"
vm storage={'storage': {}, 'nonce': '0', 'balance': '0', 'code': '0x'} gas=b'21000' stack=[] address=b'6e\xf2\xbf\x19\xee^ vE\xf3\xe65\xbf\x0fIa\xd6a\xc0' depth=0 steps=0 inst=96 pushvalue=96 pc=b'0' op=PUSH1
vm op=PUSH1 gas=b'20997' stack=[b'96'] depth=0 steps=1 inst=96 pushvalue=64 pc=b'2'
vm op=MSTORE gas=b'20994' stack=[b'96', b'64'] depth=0 steps=2 inst=82 pc=b'4'
```

Do note however that the disassembly / debugging functionality is still quite bare-bones. For manual analysis & debugging I recommend using [remix](https://remix.ethereum.org/) and [etherscan](https://etherscan.io).

#### Finding cross-references

It is often useful to know what other addresses are referenced by a particular contract. Let's say you are looking for conditions similar to the [Parity Multisig Wallet Bug](http://hackingdistributed.com/2017/07/22/deep-dive-parity-bug/). First, you want to find a list of contracts that use the `DELEGATECALL` opcode:

```
$ mythril --search "code#DELEGATECALL#"
Matched contract with code hash 05e8f07600bd384d82a71aaccaf4b3d3
Address: 0x432f96e95d249351391583cef9cbda38f26238c8, balance: 1000000000000000
Matched contract with code hash 07459966443977122e639cbf7804c446
Address: 0x76799f77587738bfeef09452df215b63d2cfb08a, balance: 1000000000000000
Address: 0x3582d2a3b67d63ed10f1ecaef0dca71b9283b543, balance: 92000000000000000000
Address: 0x4b9bc00c35f7cee95c65c3c9836040c37dec9772, balance: 89000000000000000000
Address: 0x156d5687a201affb3f1e632dcfb9fde4b0128211, balance: 29500000000000000000
(...)
```

You can then use the `--xrefs` flag to find other contracts referenced by each of those contracts:

```
$ mythril/mythril --xrefs 07459966443977122e639cbf7804c446
5b9e8728e316bbeb692d22daaab74f6cbf2c4691
```

Then, head to Etherscan to check out the source code, or use the tracer to dynamically test for issues.

## Custom scripts

By combining Mythril and [PyEthereum](https://github.com/ethereum/pyethereum) modules you can perform more complex static/dynamic analysis tasks.

-- TODO: Add example(s) --

## Issues

The RPC database sync is not a very good solution. I explored some other options, including:

- Using PyEthereum: I encountered issues syncing PyEthereum with Homestead. Also, PyEthApp only supports Python 2.7, which causes issues with other important packages.
- Accessing the Go-Ethereum LevelDB: This would be a great option. However, PyEthereum database code seems unable to deal with Go-Ethereum's LevelDB. It would take quite a bit of effort to figure this out.
- IPC might allow for faster sync then RPC - haven't tried it yet.

I'm writing this in my spare time, so contributors would be highly welcome!

## Credit

JSON RPC library is adapted from [ethjsonrpc](https://github.com/ConsenSys/ethjsonrpc) (it doesn't seem to be maintained anymore, and I needed to make some changes to it).
