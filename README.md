# Mythril

<p align="center">
	<img src="/static/mythril_new.png" height="320px"/>
</p>

[![Discord](https://img.shields.io/discord/697535391594446898)](https://discord.com/channels/697535391594446898/712829485350649886)
[![PyPI](https://badge.fury.io/py/mythril.svg)](https://pypi.python.org/pypi/mythril)
[![Read the Docs](https://readthedocs.org/projects/mythril-classic/badge/?version=master)](https://mythril-classic.readthedocs.io/en/develop/)
[![CircleCI](https://dl.circleci.com/status-badge/img/gh/Consensys/mythril/tree/develop.svg?style=shield&circle-token=fd6738fd235f6c2d8e10234259090e3b05190d0e)](https://dl.circleci.com/status-badge/redirect/gh/Consensys/mythril/tree/develop)
[![Sonarcloud - Maintainability](https://sonarcloud.io/api/project_badges/measure?project=mythril&metric=sqale_rating)](https://sonarcloud.io/dashboard?id=mythril)
[![Pypi Installs](https://static.pepy.tech/badge/mythril)](https://pepy.tech/project/mythril)
[![DockerHub Pulls](https://img.shields.io/docker/pulls/mythril/myth.svg)](https://cloud.docker.com/u/mythril/repository/docker/mythril/myth)

Mythril is a security analysis tool for EVM bytecode. It detects security vulnerabilities in smart contracts built for Ethereum, Hedera, Quorum, Vechain, Roostock, Tron and other EVM-compatible blockchains. It uses symbolic execution, SMT solving and taint analysis to detect a variety of security vulnerabilities. It's also used (in combination with other tools and techniques) in the [MythX](https://mythx.io) security analysis platform.

If you are a smart contract developer, we recommend using [MythX tools](https://github.com/b-mueller/awesome-mythx-smart-contract-security-tools) which are optimized for usability and cover a wider range of security issues.

Whether you want to contribute, need support, or want to learn what we have cooking for the future, you can checkout diligence-mythx channel in [ConsenSys Discord server](https://discord.gg/consensys).

## Installation and setup

Get it with [Docker](https://www.docker.com):

```bash
$ docker pull mythril/myth
```

Install from Pypi (Python 3.7-3.10):

```bash
$ pip3 install mythril
```

See the [docs](https://mythril-classic.readthedocs.io/en/master/installation.html) for more detailed instructions. 

## Usage

Run:

```
$ myth analyze <solidity-file>
```

Or:

```
$ myth analyze -a <contract-address>
```

Specify the maximum number of transactions to explore with `-t <number>`. You can also set a timeout with `--execution-timeout <seconds>`.

Here is an example of running Mythril on the file `killbilly.sol` which is in the `solidity_examples` directory for `3` transactions:

```
> myth a killbilly.sol -t 3
==== Unprotected Selfdestruct ====
SWC ID: 106
Severity: High
Contract: KillBilly
Function name: commencekilling()
PC address: 354
Estimated Gas Usage: 974 - 1399
Any sender can cause the contract to self-destruct.
Any sender can trigger execution of the SELFDESTRUCT instruction to destroy this contract account and withdraw its balance to an arbitrary address. Review the transaction trace generated for this issue and make sure that appropriate security controls are in place to prevent unrestricted access.
--------------------
In file: killbilly.sol:22

selfdestruct(msg.sender)

--------------------
Initial State:

Account: [CREATOR], balance: 0x2, nonce:0, storage:{}
Account: [ATTACKER], balance: 0x1001, nonce:0, storage:{}

Transaction Sequence:

Caller: [CREATOR], calldata: , decoded_data: , value: 0x0
Caller: [ATTACKER], function: killerize(address), txdata: 0x9fa299cc000000000000000000000000deadbeefdeadbeefdeadbeefdeadbeefdeadbeef, decoded_data: ('0xdeadbeefdeadbeefdeadbeefdeadbeefdeadbeef',), value: 0x0
Caller: [ATTACKER], function: activatekillability(), txdata: 0x84057065, value: 0x0
Caller: [ATTACKER], function: commencekilling(), txdata: 0x7c11da20, value: 0x0

```


Instructions for using Mythril are found on the [docs](https://mythril-classic.readthedocs.io/en/develop/). 

For support or general discussions please join the Mythril community on [Discord](https://discord.gg/E3YrVtG).

## Building the Documentation
Mythril's documentation is contained in the `docs` folder and is published to [Read the Docs](https://mythril-classic.readthedocs.io/en/develop/). It is based on Sphinx and can be built using the Makefile contained in the subdirectory:

```
cd docs
make html
```

This will create a `build` output directory containing the HTML output. Alternatively, PDF documentation can be built with `make latexpdf`. The available output format options can be seen with `make help`.

## Vulnerability Remediation

Visit the [Smart Contract Vulnerability Classification Registry](https://swcregistry.io/) to find detailed information and remediation guidance for the vulnerabilities reported.
