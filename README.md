# Mythril

<p align="center">
	<img src="/static/mythril_new.png" height="320px"/>
</p>

[![Discord](https://img.shields.io/discord/481002907366588416.svg)](https://discord.gg/E3YrVtG)
[![PyPI](https://badge.fury.io/py/mythril.svg)](https://pypi.python.org/pypi/mythril)
[![Read the Docs](https://readthedocs.org/projects/mythril-classic/badge/?version=master)](https://mythril-classic.readthedocs.io/en/master/)
![Master Build Status](https://img.shields.io/circleci/build/github/ConsenSys/mythril.svg?token=97124ecfaee54366859cae98b5dafc0714325f8b)
[![Sonarcloud - Maintainability](https://sonarcloud.io/api/project_badges/measure?project=mythril&metric=sqale_rating)](https://sonarcloud.io/dashboard?id=mythril)
[![Pypi Installs](https://pepy.tech/badge/mythril)](https://pepy.tech/project/mythril)
[![DockerHub Pulls](https://img.shields.io/docker/pulls/mythril/myth.svg?label=DockerHub&nbsp;Pulls)](https://cloud.docker.com/u/mythril/repository/docker/mythril/myth)

Mythril is a security analysis tool for EVM bytecode. It detects security vulnerabilities in smart contracts built for Ethereum, Hedera, Quorum, Vechain, Roostock, Tron and other EVM-compatible blockchains. It uses symbolic execution, SMT solving and taint analysis to detect a variety of security vulnerabilities. It's also used (in combination with other tools and techniques) in the [MythX](https://mythx.io) security analysis platform.

If you are a smart contract developer, we recommend using [MythX tools](https://github.com/b-mueller/awesome-mythx-smart-contract-security-tools) which are optimized for usability and cover a wider range of security issues.

Whether you want to contribute, need support, or want to learn what we have cooking for the future, our [Discord server](https://discord.gg/E3YrVtG) will serve your needs.

## Installation and setup

Get it with [Docker](https://www.docker.com):

```bash
$ docker pull mythril/myth
```

Install from Pypi:

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

Specify the maximum number of transaction to explore with `-t <number>`. You can also set a timeout with `--execution-timeout <seconds>`.

```
> myth a killbilly.sol -t 3
==== Unprotected Selfdestruct ====
SWC ID: 106
Severity: High
Contract: KillBilly
Function name: commencekilling()
PC address: 354
Estimated Gas Usage: 574 - 999
The contract can be killed by anyone.
Anyone can kill this contract and withdraw its balance to an arbitrary address.
--------------------
In file: killbilly.sol:22

selfdestruct(msg.sender)

--------------------
Transaction Sequence:

Caller: [CREATOR], data: [CONTRACT CREATION], value: 0x0
Caller: [ATTACKER], function: killerize(address), txdata: 0x9fa299ccbebebebebebebebebebebebedeadbeefdeadbeefdeadbeefdeadbeefdeadbeef, value: 0x0
Caller: [ATTACKER], function: activatekillability(), txdata: 0x84057065, value: 0x0
Caller: [ATTACKER], function: commencekilling(), txdata: 0x7c11da20, value: 0x0
```


Instructions for using Mythril are found on the [docs](https://mythril-classic.readthedocs.io/en/master/). 

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
