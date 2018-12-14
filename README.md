# Mythril Classic

<p align="center">
	<img src="/static/mythril_new.png" height="320px"/>
</p>

[![Discord](https://img.shields.io/discord/481002907366588416.svg)](https://discord.gg/E3YrVtG)
[![PyPI](https://badge.fury.io/py/mythril.svg)](https://pypi.python.org/pypi/mythril)
![Master Build Status](https://img.shields.io/circleci/project/github/ConsenSys/mythril-classic/master.svg)
[![Waffle.io - Columns and their card count](https://badge.waffle.io/ConsenSys/mythril-classic.svg?columns=In%20Progress)](https://waffle.io/ConsenSys/mythril-classic/)
[![Sonarcloud - Maintainability](https://sonarcloud.io/api/project_badges/measure?project=mythril&metric=sqale_rating)](https://sonarcloud.io/dashboard?id=mythril)
[![Downloads](https://pepy.tech/badge/mythril)](https://pepy.tech/project/mythril)

Mythril Classic is an open-source security analysis tool for Ethereum smart contracts. It uses concolic analysis, taint analysis and control flow checking to detect a variety of security vulnerabilities. 

Whether you want to contribute, need support, or want to learn what we have cooking for the future, our [Discord server](https://discord.gg/E3YrVtG) will serve your needs.

Oh and by the way, we're also building an easy-to-use security analysis platform (a.k.a. "the INFURA for smart contract security") that anybody can use to create purpose-built security tools. It's called [Mythril Platform](https://mythril.ai) and you should definitely [check it out](https://media.consensys.net/mythril-platform-api-is-upping-the-smart-contract-security-game-eee1d2642488).

## Installation and setup

Get it with [Docker](https://www.docker.com):

```bash
$ docker pull mythril/myth
```

Install from Pypi:

```bash
$ pip3 install mythril
```

See the [Wiki](https://github.com/ConsenSys/mythril/wiki/Installation-and-Setup) for more detailed instructions. 

## Usage

Instructions for using Mythril Classic are found on the [Wiki](https://github.com/ConsenSys/mythril-classic/wiki). 

For support or general discussions please join the Mythril community on [Discord](https://discord.gg/E3YrVtG).

## Bulding the Documentation
Mythril Classic's documentation is contained in the `docs` folder. It is based on Sphinx and can be built using the Makefile contained in the subdirectory:

```
cd docs
make html
```

This will create a `build` output directory containing the HTML output. Alternatively, PDF documentation can be built with `make latexpdf`. The available output format options can be seen with `make help`.

## Vulnerability Remediation

Visit the [Smart Contract Vulnerability Classification Registry](https://smartcontractsecurity.github.io/SWC-registry/) to find detailed information and remediation guidance for the vulnerabilities reported.
