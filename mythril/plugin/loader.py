from mythril.analysis.module import DetectionModule

from mythril.plugin.interface import MythrilPlugin, MythrilLaserPlugin
from mythril.plugin.discovery import PluginDiscovery
from mythril.support.support_utils import Singleton

from mythril.analysis.module.loader import ModuleLoader
from mythril.laser.plugin.loader import LaserPluginLoader
from typing import Dict
import logging

log = logging.getLogger(__name__)


class UnsupportedPluginType(Exception):
    """Raised when a plugin with an unsupported type is loaded"""

    pass


class MythrilPluginLoader(object, metaclass=Singleton):
    """MythrilPluginLoader singleton

    This object permits loading MythrilPlugin's
    """

    def __init__(self):
        log.info("Initializing mythril plugin loader")
        self.loaded_plugins = []
        self.plugin_args = dict()  # type: Dict[str, Dict]
        self._load_default_enabled()

    def set_args(self, plugin_name: str, **kwargs):
        self.plugin_args[plugin_name] = kwargs

    def load(self, plugin: MythrilPlugin):
        """Loads the passed plugin

        This function handles input validation and dispatches loading to type specific loaders.
        Supported plugin types:
         - laser plugins
         - detection modules
        """
        if not isinstance(plugin, MythrilPlugin):
            raise ValueError("Passed plugin is not of type MythrilPlugin")
        logging.info(f"Loading plugin: {plugin.name}")

        log.info(f"Loading plugin: {str(plugin)}")

        if isinstance(plugin, DetectionModule):
            self._load_detection_module(plugin)
        elif isinstance(plugin, MythrilLaserPlugin):
            self._load_laser_plugin(plugin)
        else:
            raise UnsupportedPluginType("Passed plugin type is not yet supported")

        self.loaded_plugins.append(plugin)
        log.info(f"Finished loading plugin: {plugin.name}")

    @staticmethod
    def _load_detection_module(plugin: DetectionModule):
        """Loads the passed detection module"""
        log.info(f"Loading detection module: {plugin.name}")
        ModuleLoader().register_module(plugin)

    @staticmethod
    def _load_laser_plugin(plugin: MythrilLaserPlugin):
        """Loads the laser plugin"""
        log.info(f"Loading laser plugin: {plugin.name}")
        LaserPluginLoader().load(plugin)

    def _load_default_enabled(self):
        """Loads the plugins that have the default enabled flag"""
        log.info("Loading installed analysis modules that are enabled by default")
        for plugin_name in PluginDiscovery().get_plugins(default_enabled=True):
            plugin = PluginDiscovery().build_plugin(
                plugin_name, self.plugin_args.get(plugin_name, {})
            )
            self.load(plugin)
