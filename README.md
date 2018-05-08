# Mythril
![Master Build Status](https://img.shields.io/circleci/project/github/ConsenSys/mythril/master.svg)
[![Join the chat at https://gitter.im/ConsenSys/mythril](https://badges.gitter.im/ConsenSys/mythril.svg)](https://gitter.im/ConsenSys/mythril?utm_source=badge&utm_medium=badge&utm_campaign=pr-badge&utm_content=badge)  [![PyPI](https://badge.fury.io/py/mythril.svg)](https://pypi.python.org/pypi/mythril)

<img height="120px" align="right" src="/static/mythril.png"/>

Mythril is a security analysis tool for Ethereum smart contracts.

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


## Acknowledgements

- JSON RPC library is adapted from [ethjsonrpc](https://github.com/ConsenSys/ethjsonrpc) (it doesn't seem to be maintained anymore, and I needed to make some changes to it).

- The signature data in `signatures.json` was initially obtained from the [Ethereum Function Signature Database](https://www.4byte.directory).

- Many features, bugfixes and analysis modules have been added by [contributors](https://github.com/b-mueller/mythril/graphs/contributors).
