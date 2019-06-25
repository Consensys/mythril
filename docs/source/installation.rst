Installation and Setup
======================

Mythril can be setup using different methods.

**************
PyPI on Mac OS
**************

.. code-block:: bash

   brew update
   brew upgrade
   brew tap ethereum/ethereum
   brew install leveldb
   brew install solidity
   pip3 install mythril


**************
PyPI on Ubuntu
**************

.. code-block:: bash

   # Update
   sudo apt update

   # Install solc
   sudo apt install software-properties-common
   sudo add-apt-repository ppa:ethereum/ethereum
   sudo apt install solc

   # Install libssl-dev, python3-dev, and python3-pip
   sudo apt install libssl-dev python3-dev python3-pip

   # Install mythril
   pip3 install mythril
   myth --version


******
Docker
******

All Mythril releases, starting from v0.18.3, are published to DockerHub as Docker images under the :code:`mythril/myth` name.

After installing `Docker CE <https://docs.docker.com/install/>`_:

   .. code-block:: bash

      # Pull the latest release of mythril/myth
      $ docker pull mythril/myth

Use :code:`docker run mythril/myth` the same way you would use the :code:`myth` command

   .. code-block:: bash

      docker run mythril/myth --help
      docker run mythril/myth disassemble -c "0x6060"

To pass a file from your host machine to the dockerized Mythril, you must mount its containing folder to the container properly. For :code:`contract.sol` in the current working directory, do:

   .. code-block:: bash

      docker run -v $(pwd):/tmp mythril/myth analyze /tmp/contract.sol
