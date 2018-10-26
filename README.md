# Mythril Classic

<p align="center">
	<img src="/static/mythril_new.png" height="320px"/>
</p>

[![Discord](https://img.shields.io/discord/481002907366588416.svg)](https://discord.gg/E3YrVtG)
[![PyPI](https://badge.fury.io/py/mythril.svg)](https://pypi.python.org/pypi/mythril)
![Master Build Status](https://img.shields.io/circleci/project/github/ConsenSys/mythril-classic/master.svg)
[![Waffle.io - Columns and their card count](https://badge.waffle.io/ConsenSys/mythril-classic.svg?columns=In%20Progress)](https://waffle.io/ConsenSys/mythril-classic/)
[![Sonarcloud - Maintainability](https://sonarcloud.io/api/project_badges/measure?project=mythril&metric=sqale_rating)](https://sonarcloud.io/dashboard?id=mythril)
[![PyPI Statistics](https://pypistats.com/badge/mythril.svg)](https://pypistats.com/package/mythril)

Mythril Classic is an open-source security analysis tool for Ethereum smart contracts. It uses concolic analysis, taint analysis and control flow checking to detect a variety of security vulnerabilities. 

Whether you want to contribute, need support, or want to learn what we have cooking for the future, our [Discord server](https://discord.gg/E3YrVtG) will serve your needs!

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

Instructions for using the 'myth' tool are found on the [Wiki](https://github.com/ConsenSys/mythril-classic/wiki). 

For support or general discussions please join the Mythril community on [Discord](https://discord.gg/E3YrVtG).

## Vulnerability Remediation

Visit the [Smart Contract Vulnerability Classification Registry](https://smartcontractsecurity.github.io/SWC-registry/) to find detailed information and remediation guidance for the vulnerabilities reported.

## Presentations, papers and articles

- [Analyzing Ethereum Smart Contracts for Vulnerabilities](https://hackernoon.com/scanning-ethereum-smart-contracts-for-vulnerabilities-b5caefd995df)
- [What Caused the Parity SUICIDE Vulnerability & How to Detect Similar Bugs](https://hackernoon.com/what-caused-the-latest-100-million-ethereum-bug-and-a-detection-tool-for-similar-bugs-7b80f8ab7279)
- [Detecting Integer Overflows in Ethereum Smart Contracts](https://media.consensys.net/detecting-batchoverflow-and-similar-flaws-in-ethereum-smart-contracts-93cf5a5aaac8)
- [How Formal Verification Can Ensure Flawless Smart Contracts](https://media.consensys.net/how-formal-verification-can-ensure-flawless-smart-contracts-cbda8ad99bd1)
- [Smashing Smart Contracts for Fun and Real Profit](https://hackernoon.com/hitb2018ams-smashing-smart-contracts-for-fun-and-real-profit-720f5e3ac777)
- [HITBSecConf 2018 - Presentation video](https://www.youtube.com/watch?v=iqf6epACgds)
- [EDCon Toronto 2018 - Mythril: Find bugs and verify security properties in your contracts](https://www.youtube.com/watch?v=NJ9StJThxZY&feature=youtu.be&t=3h3m18s)

