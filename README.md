# Mythril
![Master Build Status](https://img.shields.io/circleci/project/github/ConsenSys/mythril/master.svg)
[![Join the chat at https://gitter.im/ConsenSys/mythril](https://badges.gitter.im/ConsenSys/mythril.svg)](https://gitter.im/ConsenSys/mythril?utm_source=badge&utm_medium=badge&utm_campaign=pr-badge&utm_content=badge)  [![PyPI](https://badge.fury.io/py/mythril.svg)](https://pypi.python.org/pypi/mythril)

<img height="120px" align="right" src="/static/mythril.png"/>

Mythril is a security analysis tool for Ethereum smart contracts. It uses concolic analysis, taint analysis and control flow checking to detect a variety of security vulnerabilities. The analysis is based on [laser-ethereum](https://github.com/b-mueller/laser-ethereum), a symbolic execution library for EVM bytecode.

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

See the [Wiki](https://github.com/ConsenSys/mythril/wiki/Installation-and-Setup) for more detailed instructions. 

## Usage

Documentation has moved to the [Wiki page](https://github.com/ConsenSys/mythril/wiki).

## Publications and Videos

- [HITBSecConf 2018 - Smashing Ethereum smart contracts for fun and real profit](https://www.youtube.com/watch?v=iqf6epACgds)
- [HITBSecConf 2018 conference paper](https://github.com/b-mueller/smashing-smart-contracts/blob/master/smashing-smart-contracts-1of1.pdf)
- [EDCon Toronto 2018 - Mythril: Find bugs and verify security properties in your contracts](https://www.youtube.com/watch?v=NJ9StJThxZY&feature=youtu.be&t=3h3m18s)

# Mythril is Hiring

[ConsenSys Diligence](https://consensys.net/diligence/) is building a dedicated Mythril team. If you're a coder and/or Ethereum security enthusiast who wants to do interesting and challenging work for a decentralized organization, check out the open positions below. You can apply directly on the website or ping b-mueller on [Gitter](https://gitter.im/ConsenSys/mythril).

- [Developer - Security Analysis Tools](https://new.consensys.net/careers/?gh_jid=1129067)
- [Developer - Security Analysis Tools (Part Time)](https://new.consensys.net/careers/?gh_jid=1129048)
- [Lead Developer - Security Analysis Engine](https://new.consensys.net/careers/?gh_jid=1127291)
- [Lead Software Engineer - Auditor Security Tools](https://new.consensys.net/careers/?gh_jid=1127282)
