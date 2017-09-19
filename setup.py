from setuptools import setup, find_packages
from codecs import open
import os


long_description = '''
Mythril
=======

Mythril is an assembler and disassembler for Ethereum VM bytecode. It was created for low-level
testing/fuzzing of EVM implementations.

Installation
------------

Install from Pypi:

.. code:: bash

    $ pip install mythril

Or, clone the GitHub repo to install the newest master branch:

.. code:: bash

    $ git clone https://github.com/b-mueller/mythril/
    $ cd mythril
    $ python setup.py install

Usage
-----

To disassemble a piece of bytecode, pass it on the command line:

.. code:: bash

    $ mythril -d -c "0x606060405050"
    PUSH1 0x60
    PUSH1 0x40
    POP
    POP

Modifying and re-assembling code
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Mythril can assemble code from input files that contain one instruction per line. To start from an
existing contract, save the disassembly to a text file:

.. code:: bash

    $ mythril -d -c "0x606060405050" -o code.easm

Edit the instructions in a text editor. For example, we can modify the ``PUSH`` instructions from
the original example:

::

    PUSH2 0x4050
    PUSH4 0x60708090
    POP
    POP

Save the file and run Mythril with the ``-a`` flag to re-assemble:

::

    $ mythril -a code.easm 
    0x61405063607080905050

The virtual machine language is described in the `Ethereum
Yellowpaper <http://gavwood.com/paper.pdf>`__.

Tracing EVM execution
~~~~~~~~~~~~~~~~~~~~~

You can run a piece of bytecode in the `PyEthereum <https://github.com/ethereum/pyethereum>`__ VM
and trace its execution using the ``-t`` flag. This will output the instructions executed as well as
the state of the stack for every execution step. To run code from the command line, use:

.. code:: bash

    $ ./mythril.py -t -c "0x606060405050"
    vm stack=[] op=PUSH1 steps=0 pc=b'0' address=b'\x01#Eg\x89\xab\xcd\xef\x01#Eg\x89\xab\xcd\xef\x01#Eg' depth=0 pushvalue=96 gas=b'1000000' storage={'code': '0x', 'nonce': '0', 'balance': '0', 'storage': {}} inst=96
    vm stack=[b'96'] op=PUSH1 steps=1 depth=0 pushvalue=64 gas=b'999997' pc=b'2' inst=96
    vm stack=[b'96', b'64'] op=POP steps=2 depth=0 gas=b'999994' pc=b'4' inst=80
    vm stack=[b'96'] op=POP steps=3 depth=0 gas=b'999992' pc=b'5' inst=80

For larger contracts, you might prefer to compile them to a binary file instead:

::

    $ mythril -a contract.easm -o contract.bin
    $ mythril --trace -f contract.bin

Disassembling a contract from the Ethereum blockchain
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

You can also load code from an existing contract in the Ethereum blockchain. For this, you need to
have a full node running, and the RPC debug interface must be activated. For example, when running
``geth`` you can do this as follows:

.. code:: bash

    $ geth --syncmode full --rpc --rpcapi eth,debug

To load contract code from your node, pass the TxID of the transaction that created the contract:

.. code:: bash

    $ mythril -d --txid 0x23112645da9ae684270de843faaeb44918c79a09e019d3a6cf8b87041020340e -o some_contract.easm

Note: If you want to get code from the Ethereum mainnet, it is easier to download it from
`Etherscan <https://etherscan.io>`__.

Credit
------

JSON RPC library is adapted from `ethjsonrpc <https://github.com/ConsenSys/ethjsonrpc>`__ (it
doesn't seem to be maintained anymore, and I needed to make some changes to it).
'''


setup(
    name='mythril',

    version='0.1.1',

    description='Mythril is an assembler and disassembler for Ethereum VM bytecode',
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

    keywords='hacking disassmbler ethereum',

    packages=find_packages(exclude=['contrib', 'docs', 'tests']),

    install_requires=[
        'ethereum==2.0.4',
    ],

    extras_require={
    },

    scripts=['mythril']
)
