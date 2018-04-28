from setuptools import setup, find_packages
from setuptools.command.install import install
import os

# Package version (vX.Y.Z). It must match git tag being used for CircleCI
# deployment; otherwise the build will failed.
VERSION = "v0.16.26"

class VerifyVersionCommand(install):
  """Custom command to verify that the git tag matches our version"""
  description = 'verify that the git tag matches our version'

  def run(self):
      tag = os.getenv('CIRCLE_TAG')

      if (tag != VERSION):
          info = "Git tag: {0} does not match the version of this app: {1}".format(tag, VERSION)
          sys.exit(info)

long_description = '''
Mythril is a security analysis tool for Ethereum smart contracts. It
uses concolic analysis to detect various types of issues. Use it to
analyze source code or as a nmap-style black-box blockchain scanner (an
"ethermap" if you will).

Installation and setup
----------------------

Install from Pypi:

.. code:: bash

    $ pip install mythril

Or, clone the GitHub repo to install the newest master branch:

.. code:: bash

    $ git clone https://github.com/b-mueller/mythril/
    $ cd mythril
    $ python setup.py install

Note that Mythril requires Python 3.5 to work.

Function signatures
~~~~~~~~~~~~~~~~~~~

Whenever you disassemble or analyze binary code, Mythril will try to
resolve function names using its local signature database. The database
must be provided at ``~/.mythril/signatures.json``. You can start out
with the `default file <signatures.json>`__ as follows:

::

    $ cd ~/.mythril
    $ wget https://raw.githubusercontent.com/b-mueller/mythril/master/signatures.json

When you analyze Solidity code, new function signatures are added to the
database automatically.

Security analysis
-----------------

Run ``myth -x`` with one of the input options described below to run the
analysis. This will run the Python modules in the
`/analysis/modules <https://github.com/b-mueller/mythril/tree/master/mythril/analysis/modules>`__
directory.

Mythril detects a range of `security issues <security_checks.md>`__,
including integer underflows, owner-overwrite-to-Ether-withdrawal, and
others. However, the analysis will not detect business logic issues and
is not equivalent to formal verification.

Analyzing Solidity code
~~~~~~~~~~~~~~~~~~~~~~~

In order to work with Solidity source code files, the `solc command line
compiler <http://solidity.readthedocs.io/en/develop/using-the-compiler.html>`__
needs to be installed and in path. You can then provide the source
file(s) as positional arguments, e.g.:

.. code:: bash

    $ myth -x myContract.sol

Alternatively, compile the code on `Remix <http://remix.ethereum.org>`__
and pass the runtime binary code to Mythril:

.. code:: bash

    $ myth -x -c "0x5060(...)"

If you have multiple interdependent contracts, pass them to Mythril as
separate input files. Mythril will map the first contract to address
"0x0000(..)", the second one to "0x1111(...)", and so forth (make sure
that contract addresses are set accordingly in the source). The contract
passed in the first argument will be executed as the "main" contract.

.. code:: bash

    $ myth -x myContract.sol myLibrary.sol

Working with on-chain contracts
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

To analyze contracts on the blockchain you need an Ethereum node. By
default, Mythril will query a local node via RPC. Alternatively, you can
use `INFURA <https://infura.io>`__:

::

    $ myth --infura-mainnet -x -a 0x5c436ff914c458983414019195e0f4ecbef9e6dd

If you are planning to do batch operations or use the contract search
features, running a
`go-ethereum <https://github.com/ethereum/go-ethereum>`__ node is
recommended. Start your local node as follows:

.. code:: bash

    $ geth --rpc --rpcapi eth,debug --syncmode fast

Specify the target contract with the ``-a`` option:

.. code:: bash

    $ myth -x -a 0x5c436ff914c458983414019195e0f4ecbef9e6dd -v1

Adding the ``-l`` flag will cause Mythril to automatically retrieve
dependencies, such as library contracts:

.. code:: bash

    $  myth -x -a 0xEbFD99838cb0c132016B9E117563CB41f2B02264 -l -v1

Control flow graph
------------------

The ``-g FILENAME`` option generates an `interactive jsViz
graph <http://htmlpreview.github.io/?https://github.com/b-mueller/mythril/blob/master/static/mythril.html>`__:

.. code:: bash

    $ myth -g ./graph.html -a 0xEbFD99838cb0c132016B9E117563CB41f2B02264 -l

.. figure:: https://raw.githubusercontent.com/b-mueller/mythril/master/static/callgraph7.png
   :alt: Call graph

   callgraph

[STRIKEOUT:The "bounce" effect, while awesome (and thus enabled by
default), sometimes messes up the graph layout.] Try adding the
``--enable-physics`` flag for a very entertaining "bounce" effect that
unfortunately completely destroys usability.

Blockchain exploration
----------------------

Mythril builds its own contract database to enable fast search
operations. This enables operations like those described in the
`legendary "Mitch Brenner" blog
post <https://medium.com/@rtaylor30/how-i-snatched-your-153-037-eth-after-a-bad-tinder-date-d1d84422a50b>`__
in [STRIKEOUT:seconds] minutes instead of days. Unfortunately, the
initial sync process is slow. You don't need to sync the whole
blockchain right away though: If you abort the syncing process with
``ctrl+c``, it will be auto-resumed the next time you run the
``--init-db`` command.

.. code:: bash

    $ myth --init-db
    Starting synchronization from latest block: 4323706
    Processing block 4323000, 3 individual contracts in database
    (...)

The default behavior is to only sync contracts with a non-zero balance.
You can disable this behavior with the ``--sync-all`` flag, but be aware
that this will result in a huge (as in: dozens of GB) database.

Searching from the command line
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The search feature allows you to find contract instances that contain
specific function calls and opcode sequences. It supports simple boolean
expressions, such as:

.. code:: bash

    $ myth --search "func#changeMultisig(address)#"
    $ myth --search "code#PUSH1 0x50,POP#"
    $ myth --search "func#changeMultisig(address)# and code#PUSH1 0x50#"

Reading contract storage
~~~~~~~~~~~~~~~~~~~~~~~~

You can read the contents of storage slots from a deployed contract as
follows.

.. code:: bash

    ./myth --storage 0 -a "0x76799f77587738bfeef09452df215b63d2cfb08a"
    0x0000000000000000000000000000000000000000000000000000000000000003

Utilities
---------

Disassembler
~~~~~~~~~~~~

Use the ``-d`` flag to disassemble code. The disassembler accepts a
bytecode string or a contract address as its input.

.. code:: bash

    $ myth -d -c "0x6060"
    0 PUSH1 0x60

Specifying an address via ``-a ADDRESS`` will download the contract code
from your node.

.. code:: bash

    $ myth -d -a "0x2a0c0dbecc7e4d658f48e01e3fa353f44050c208"
    0 PUSH1 0x60
    2 PUSH1 0x40
    4 MSTORE
    (...)
    1135 - FUNCTION safeAdd(uint256,uint256) -
    1136 CALLVALUE
    1137 ISZERO

Finding cross-references
~~~~~~~~~~~~~~~~~~~~~~~~

It is often useful to find other contracts referenced by a particular
contract. E.g.:

.. code:: bash

    $ myth --search "code#DELEGATECALL#"
    Matched contract with code hash 07459966443977122e639cbf7804c446
    Address: 0x76799f77587738bfeef09452df215b63d2cfb08a, balance: 1000000000000000
    $ myth --xrefs -a 0x76799f77587738bfeef09452df215b63d2cfb08a
    5b9e8728e316bbeb692d22daaab74f6cbf2c4691

Calculating function hashes
~~~~~~~~~~~~~~~~~~~~~~~~~~~

To print the Keccak hash for a given function signature:

.. code:: bash

    $ myth --hash "setOwner(address)"
    0x13af4035

Credit
------

-  JSON RPC library is adapted from
   `ethjsonrpc <https://github.com/ConsenSys/ethjsonrpc>`__ (it doesn't
   seem to be maintained anymore, and I needed to make some changes to
   it).

-  The signature data in ``signatures.json`` was initially obtained from
   the `Ethereum Function Signature
   Database <https://www.4byte.directory>`__.
'''


setup(
    name='mythril',

    version=VERSION[1:],

    description='Security analysis tool for Ethereum smart contracts',
    long_description=long_description,

    url='https://github.com/b-mueller/mythril',

    author='Bernhard Mueller',
    author_email='bernhard.mueller11@gmail.com',

    license='MIT',

    classifiers=[
        'Development Status :: 3 - Alpha',

        'Intended Audience :: Science/Research',
        'Topic :: Software Development :: Disassemblers',

        'License :: OSI Approved :: MIT License',

        'Programming Language :: Python :: 2',
        'Programming Language :: Python :: 2.7',
        'Programming Language :: Python :: 3',
        'Programming Language :: Python :: 3.3',
        'Programming Language :: Python :: 3.4',
        'Programming Language :: Python :: 3.5',
    ],

    keywords='hacking disassembler security ethereum',

    packages=find_packages(exclude=['contrib', 'docs', 'tests']),

    install_requires=[
        'ethereum>=2.3.0',
        'ZODB>=5.3.0',
        'z3-solver>=4.5',
        'laser-ethereum>=0.5.20',
        'requests',
        'BTrees',
        'py-solc',
        'plyvel',
        'pytest',
        'eth_abi>=1.0.0',
        'eth-utils>=1.0.1',
        'eth-account>=0.1.0a2',
        'eth-hash>=0.1.0',
        'eth-keyfile>=0.5.1',
        'eth-keys>=0.2.0b3',
        'eth-rlp>=0.1.0',
        'eth-tester>=0.1.0b21',
        'coverage',
        'jinja2',
        'attrs',
        'rlp<1.0.0'
    ],

    python_requires='>=3.5',

    extras_require={
    },

    include_package_data=True,

    scripts=['myth'],

    cmdclass = {
      'verify': VerifyVersionCommand,
    }
)
