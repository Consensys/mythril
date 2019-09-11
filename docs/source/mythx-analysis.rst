MythX Analysis
=================

Run :code:`myth pro` with one of the input options described below will run a `MythX analysis <https://mythx.io>`_ on the desired input. This includes a run of Mythril, the fuzzer Harvey, and the static analysis engine Maru and has some false-positive filtering only possible by combining the tool capabilities.

**************
Authentication
**************

In order to authenticate with the MythX API, set the environment variables ``MYTHX_PASSWORD`` and ``MYTHX_ETH_ADDRESS``.

.. code-block:: bash

   $ export MYTHX_ETH_ADDRESS='0x0000000000000000000000000000000000000000'
   $ export MYTHX_PASSWORD='password'

***********************
Analyzing Solidity Code
***********************

The input format is the same as a regular Mythril analysis.

.. code-block:: bash

   $ myth pro ether_send.sol
   ==== Unprotected Ether Withdrawal ====
   SWC ID: 105
   Severity: High
   Contract: Crowdfunding
   Function name: withdrawfunds()
   PC address: 730
   Anyone can withdraw ETH from the contract account.
   Arbitrary senders other than the contract creator can withdraw ETH from the contract account without previously having sent an equivalent amount of ETH to it. This is likely to be a vulnerability.
   --------------------
   In file: tests/testdata/input_contracts/ether_send.sol:21

   msg.sender.transfer(address(this).balance)

   --------------------

If an input file contains multiple contract definitions, Mythril analyzes the *last* bytecode output produced by solc. You can override this by specifying the contract name explicitly:

.. code-block:: bash

   myth pro OmiseGo.sol:OMGToken

To specify a contract address, use :code:`-a <address>`

****************************
Analyzing On-Chain Contracts
****************************

Analyzing a mainnet contract via INFURA:

.. code-block:: bash

   myth pro -a 0x5c436ff914c458983414019195e0f4ecbef9e6dd

Adding the :code:`-l` flag will cause mythril to automatically retrieve dependencies, such as dynamically linked library contracts:

.. code-block:: bash

   myth -v4 pro -l -a 0xEbFD99838cb0c132016B9E117563CB41f2B02264
