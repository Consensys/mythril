# Mythril

<img height="60px" align="right" src="/static/mythril.png"/>

Mythril is a bug hunting tool and framework for the Ethereum blockchain.

## Be responsible!

The purpose of this tool is to aid discovery of vulnerable smart contracts on the Ethereum mainnet and support research for novel security flaws. If you do find an exploitable issue, please [do the right thing](https://en.wikipedia.org/wiki/Responsible_disclosure), and don't attempt to brand it with a name like "etherbleed" or "chainshock".

## Installation and setup

Install from Pypi:

```bash
$ pip install mythril
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

### Other commands

You can also disassemble and trace code using the '-d' and '-t' flags, respectively. When tracing, the code is run in the PyEthereum virtual machine with the (optional) input data passed via the '--data' flag.

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

Do note however that the disassembly / debugging functionality is currently quite bare-bones. If you are planning to do manual analysis, I recommend using [remix](https://remix.ethereum.org/) and [etherscan](https://etherscan.io).

## Custom scripts

By combining modules of Mythril and [PyEthereum](https://github.com/ethereum/pyethereum) you can perform more complex static/dynamic analysis tasks.

-- TODO: Add example(s) --

## Credit

JSON RPC library is adapted from [ethjsonrpc](https://github.com/ConsenSys/ethjsonrpc) (it doesn't seem to be maintained anymore, and I needed to make some changes to it).
