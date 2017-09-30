# Mythril

Mythril is a bug hunting tool and framework for the Ethereum blockchain.

## Be responsible!



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

Mythril builds its own contract database using RPC sync. Unfortunately, this process is slow - however, you don't need to sync the whole blockchain to start working. If you abort the syncing process with `ctrl+c`, it will auto-resume the next time you run the `--init-db` command.

```bash
$ mythril --init-db
Starting synchronization from latest block: 4323706
Processing block 4323000, 3 individual contracts in database
(...)
```

The default behavior is to only sync contracts with a non-zero balance. You can disable this behaviour with the `--sync-all` flag, but note that this will result in a very large (multi-gigabyte) database.

## Command line usage

The `mythril` command line tool allows you to easily access most of Mythril's functionality.

### Searching the database

The search feature allows you to find contract instances that contain specific function calls and opcode sequences. It supports simple boolean expressions, such as:

```bash
$ mythril --search "func[changeMultisig(address)]"
$ mythril --search "code[PUSH1 0x50,POP]"
$ mythril --search "func[changeMultisig(address)] and code[PUSH1 0x50,POP]"
```

### Tracing code in the EVM

```
$ ./mythril -d -a "0x3665f2bf19ee5e207645f3e635bf0f4961d661c0"
PUSH1 0x60
PUSH1 0x40
MSTORE
CALLDATASIZE
ISZERO
PUSH2 0x00ac
JUMPI
(...)
```

## Custom scripts

-- TODO --

## Credit

JSON RPC library is adapted from [ethjsonrpc](https://github.com/ConsenSys/ethjsonrpc) (it doesn't seem to be maintained anymore, and I needed to make some changes to it).
