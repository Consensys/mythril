import codecs
import logging
import os
import platform
import re

from pathlib import Path
from shutil import copyfile
from configparser import ConfigParser
from typing import Optional

from mythril.exceptions import CriticalError
from mythril.ethereum.interface.rpc.client import EthJsonRpc
from mythril.ethereum.interface.leveldb.client import EthLevelDB

log = logging.getLogger(__name__)


class MythrilConfig:
    def __init__(self):
        self.mythril_dir = self._init_mythril_dir()
        self.config_path = os.path.join(self.mythril_dir, "config.ini")
        self.leveldb_dir = self._init_config()
        self.eth = None  # type: Optional[EthJsonRpc]
        self.eth_db = None  # type: Optional[EthLevelDB]

    @staticmethod
    def _init_mythril_dir() -> str:
        """
        Initializes the mythril dir and config.ini file
        :return: The mythril dir's path
        """

        try:
            mythril_dir = os.environ["MYTHRIL_DIR"]
        except KeyError:
            mythril_dir = os.path.join(os.path.expanduser("~"), ".mythril")

        if not os.path.exists(mythril_dir):
            # Initialize data directory
            log.info("Creating mythril data directory")
            os.mkdir(mythril_dir)

        db_path = str(Path(mythril_dir) / "signatures.db")
        if not os.path.exists(db_path):
            # if the default mythril dir doesn't contain a signature DB
            # initialize it with the default one from the project root
            asset_dir = Path(__file__).parent.parent / "support" / "assets"
            copyfile(str(asset_dir / "signatures.db"), db_path)

        return mythril_dir

    def _init_config(self) -> str:
        """If no config file exists, create it and add default options.

        Default LevelDB path is specified based on OS
        dynamic loading is set to infura by default in the file
        :return: LevelDB directory
        """

        leveldb_fallback_dir = self._get_fallback_dir()

        if not os.path.exists(self.config_path):
            log.info("No config file found. Creating default: " + self.config_path)
            open(self.config_path, "a").close()

        config = ConfigParser(allow_no_value=True)
        # TODO: Remove this after this issue https://github.com/python/mypy/issues/2427 is closed
        config.optionxform = str  # type:ignore
        config.read(self.config_path, "utf-8")
        if "defaults" not in config.sections():
            self._add_default_options(config)

        if not config.has_option("defaults", "leveldb_dir"):
            self._add_leveldb_option(config, leveldb_fallback_dir)

        if not config.has_option("defaults", "dynamic_loading"):
            self._add_dynamic_loading_option(config)

        with codecs.open(self.config_path, "w", "utf-8") as fp:
            config.write(fp)

        leveldb_dir = config.get(
            "defaults", "leveldb_dir", fallback=leveldb_fallback_dir
        )
        return os.path.expanduser(leveldb_dir)

    @staticmethod
    def _get_fallback_dir() -> str:
        """
        Returns the LevelDB path
        :return: The LevelDB path
        """
        system = platform.system().lower()
        leveldb_fallback_dir = os.path.expanduser("~")
        if system.startswith("darwin"):
            leveldb_fallback_dir = os.path.join(
                leveldb_fallback_dir, "Library", "Ethereum"
            )
        elif system.startswith("windows"):
            leveldb_fallback_dir = os.path.join(
                leveldb_fallback_dir, "AppData", "Roaming", "Ethereum"
            )
        else:
            leveldb_fallback_dir = os.path.join(leveldb_fallback_dir, ".ethereum")
        return os.path.join(leveldb_fallback_dir, "geth", "chaindata")

    @staticmethod
    def _add_default_options(config: ConfigParser) -> None:
        """
        Adds defaults option to config.ini
        :param config: The config file object
        :return: None
        """
        config.add_section("defaults")

    @staticmethod
    def _add_leveldb_option(config: ConfigParser, leveldb_fallback_dir: str) -> None:
        """
        Sets a default leveldb path in .mythril/config.ini file
        :param config: The config file object
        :param leveldb_fallback_dir: The leveldb dir to use by default for searches
        :return: None
        """
        config.set("defaults", "#Default chaindata locations:", "")
        config.set("defaults", "#– Mac: ~/Library/Ethereum/geth/chaindata", "")
        config.set("defaults", "#– Linux: ~/.ethereum/geth/chaindata", "")
        config.set(
            "defaults",
            "#– Windows: %USERPROFILE%\\AppData\\Roaming\\Ethereum\\geth\\chaindata",
            "",
        )
        config.set("defaults", "leveldb_dir", leveldb_fallback_dir)

    @staticmethod
    def _add_dynamic_loading_option(config: ConfigParser) -> None:
        """
        Sets the dynamic loading config option in .mythril/config.ini file
        :param config: The config file object
        :return: None
        """
        config.set(
            "defaults", "#– To connect to Infura use dynamic_loading: infura", ""
        )
        config.set(
            "defaults",
            "#– To connect to Rpc use "
            "dynamic_loading: HOST:PORT / ganache / infura-[network_name]",
            "",
        )
        config.set(
            "defaults", "#– To connect to local host use dynamic_loading: localhost", ""
        )
        config.set("defaults", "dynamic_loading", "infura")

    def set_api_leveldb(self, leveldb_path: str) -> None:
        """
        """
        self.eth_db = EthLevelDB(leveldb_path)

    def set_api_rpc_infura(self) -> None:
        """Set the RPC mode to INFURA on Mainnet."""
        log.info("Using INFURA Main Net for RPC queries")
        self.eth = EthJsonRpc("mainnet.infura.io", 443, True)

    def set_api_rpc(self, rpc: str = None, rpctls: bool = False) -> None:
        """
        Sets the RPC mode to either of ganache or infura
        :param rpc: either of the strings - ganache, infura-mainnet, infura-rinkeby, infura-kovan, infura-ropsten
        """
        if rpc == "ganache":
            rpcconfig = ("localhost", 8545, False)
        else:
            m = re.match(r"infura-(.*)", rpc)
            if m and m.group(1) in ["mainnet", "rinkeby", "kovan", "ropsten"]:
                rpcconfig = (m.group(1) + ".infura.io", 443, True)
            else:
                try:
                    host, port = rpc.split(":")
                    rpcconfig = (host, int(port), rpctls)
                except ValueError:
                    raise CriticalError(
                        "Invalid RPC argument, use 'ganache', 'infura-[network]' or 'HOST:PORT'"
                    )

        if rpcconfig:
            log.info("Using RPC settings: %s" % str(rpcconfig))
            self.eth = EthJsonRpc(rpcconfig[0], int(rpcconfig[1]), rpcconfig[2])
        else:
            raise CriticalError("Invalid RPC settings, check help for details.")

    def set_api_rpc_localhost(self) -> None:
        """Set the RPC mode to a local instance."""
        log.info("Using default RPC settings: http://localhost:8545")
        self.eth = EthJsonRpc("localhost", 8545)

    def set_api_from_config_path(self) -> None:
        """Set the RPC mode based on a given config file."""
        config = ConfigParser(allow_no_value=False)
        # TODO: Remove this after this issue https://github.com/python/mypy/issues/2427 is closed
        config.optionxform = str  # type:ignore
        config.read(self.config_path, "utf-8")
        if config.has_option("defaults", "dynamic_loading"):
            dynamic_loading = config.get("defaults", "dynamic_loading")
        else:
            dynamic_loading = "infura"
        self._set_rpc(dynamic_loading)

    def _set_rpc(self, rpc_type: str) -> None:
        """
        Sets rpc based on the type
        :param rpc_type: The type of connection: like infura, ganache, localhost
        :return:
        """
        if rpc_type == "infura":
            self.set_api_rpc_infura()
        elif rpc_type == "localhost":
            self.set_api_rpc_localhost()
        else:
            self.set_api_rpc(rpc_type)
