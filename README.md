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

Mythril is a security analysis tool for EVM bytecode. It detects security vulnerabilities in smart contracts built for Ethereum, Quorum, Vechain, Roostock, Tron and other EVM-compatible blockchains. It uses symbolic execution, SMT solving and taint analysis detect a variety of security vulnerabilities. It's also used (in combination with other tools and techniques) in the [MythX](https://mythx.io) security analysis platform.

If you are a smart contract developer, we recommend using [MythX tools](https://github.com/b-mueller/awesome-mythx-smart-contract-security) which are optimized for usability and cover a wider range of security issues.

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

See the [Wiki](https://github.com/ConsenSys/mythril/wiki/Installation-and-Setup) for more detailed instructions. 

## Usage

Instructions for using Mythril are found on the [Wiki](https://github.com/ConsenSys/mythril/wiki). 

For support or general discussions please join the Mythril community on [Discord](https://discord.gg/E3YrVtG).

## Bulding the Documentation
Mythril's documentation is contained in the `docs` folder and is published to [Read the Docs](https://mythril-classic.readthedocs.io/en/master/). It is based on Sphinx and can be built using the Makefile contained in the subdirectory:

```
cd docs
make html
```

This will create a `build` output directory containing the HTML output. Alternatively, PDF documentation can be built with `make latexpdf`. The available output format options can be seen with `make help`.

## Vulnerability Remediation

Visit the [Smart Contract Vulnerability Classification Registry](https://smartcontractsecurity.github.io/SWC-registry/) to find detailed information and remediation guidance for the vulnerabilities reported.
