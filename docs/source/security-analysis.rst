Security Analysis
=================

Run :code:`myth -x` with one of the input options described below will run the analysis modules in the `/analysis/modules <https://github.com/ConsenSys/mythril/tree/master/mythril/analysis/modules>`_ directory.

***********************
Analyzing Solidity Code
***********************

In order to work with Solidity source code files, the `solc command line compiler <https://solidity.readthedocs.io/en/develop/using-the-compiler.html>`_ needs to be installed and in PATH. You can then provide the source file(s) as positional arguments.

.. code-block:: bash

   $ myth -x ether_send.sol
   ==== Unprotected Ether Withdrawal ====
   SWC ID: 105
   Severity: High
   Contract: Crowdfunding
   Function name: withdrawfunds()
   PC address: 730
   Estimated Gas Usage: 1132 - 1743
   Anyone can withdraw ETH from the contract account.
   Arbitrary senders other than the contract creator can withdraw ETH from the contract account without previously having sent an equivalent amount of ETH to it. This is likely to be a vulnerability.
   --------------------
   In file: tests/testdata/input_contracts/ether_send.sol:21

   msg.sender.transfer(address(this).balance)

   --------------------

If an input file contains multiple contract definitions, Mythril analyzes the *last* bytecode output produced by solc. You can override this by specifying the contract name explicitly:

.. code-block:: bash

   myth -x OmiseGo.sol:OMGToken

Specifying Solc Versions
########################

You can specify a version of the solidity compiler to be used with :code:`--solv <version number>`. Please be aware that this uses `py-solc <https://github.com/ethereum/py-solc>`_ and will only work on Linux and macOS. It will check the version of solc in your path, and if this is not what is specified, it will download binaries on Linux or try to compile from source on macOS.


Output Formats
##############

By default, analysis results are printed to the terminal in text format. You can change the output format with the :code:`-o` argument:

.. code-block:: bash

   myth -xo jsonv2 underflow.sol

Available formats are :code:`text`, :code:`markdown`, :code:`json`, and :code:`jsonv2`. For integration with other tools, :code:`jsonv2` is generally preferred over :code:`json` because it is consistent with other `MythX <https://mythx.io>`_ tools.

****************************
Analyzing On-Chain Contracts
****************************

When analyzing contracts on the blockchain, Mythril will by default attempt to query INFURA. You can use the built-in INFURA support or manually configure the RPC settings with the :code:`--rpc` argument.

+--------------------------------+-------------------------------------------------+
| :code:`--rpc ganache`          | Connect to local Ganache                        |
+--------------------------------+-------------------------------------------------+
| :code:`--rpc infura-[netname]` | Connect to mainnet, rinkeby, kovan, or ropsten. |
+--------------------------------+-------------------------------------------------+
| :code:`--rpc host:port`        | Connect to custom rpc                           |
+--------------------------------+-------------------------------------------------+
| :code:`--rpctls <True/False>`  | RPC connection over TLS (default: False)        |
+--------------------------------+-------------------------------------------------+

To specify a contract address, use :code:`-a <address>`

Analyze mainnet contract via INFURA:

.. code-block:: bash

   myth -x -a 0x5c436ff914c458983414019195e0f4ecbef9e6dd

Adding the :code:`-l` flag will cause mythril to automatically retrieve dependencies, such as dynamically linked library contracts:

.. code-block:: bash

   myth -xla 0xEbFD99838cb0c132016B9E117563CB41f2B02264 -v4

******************
Speed vs. Coverage
******************

The execution timeout can be specified with the :code:`--execution-timeout <seconds>` argument. When the timeout is reached, mythril will stop analysis and print out all currently found issues.

The maximum recursion depth for the symbolic execution engine can be controlled with the :code:`--max-depth` argument. The default value is 22. Lowering this value will decrease the number of explored states and analysis time, while increasing this number will increase the number of explored states and increase analysis time. For some contracts, it helps to fine tune this number to get the best analysis results.
