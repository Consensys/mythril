from mythril.analysis.module import DetectionModule

from mythril.plugin.interface import MythrilCLIPlugin, MythrilPlugin
from mythril.plugin.discovery import PluginDiscovery
from mythril.support.support_utils import Singleton

import logging

log = logging.getLogger(__name__)


class UnsupportedPluginType(Exception):
    pass


class MythrilPluginLoader(object, metaclass=Singleton):
    """MythrilPluginLoader singleton

    This object permits loading MythrilPlugin's
    """

    def __init__(self):
        log.info("Initializing mythril plugin loader")
        self.loaded_plugins = []
        self._load_default_enabled()

    def load(self, plugin: MythrilPlugin):
        """Loads the passed plugin"""
        logging.info(f"Loading plugin: {plugin.name}")
        if not isinstance(plugin, MythrilPlugin):
            raise ValueError("Passed plugin is not of type MythrilPlugin")

        log.info(f"Loading plugin: {str(plugin)}")

        if isinstance(plugin, DetectionModule):
            self._load_detection_module(plugin)
        else:
            raise UnsupportedPluginType("Passed plugin type is not yet supported")

        self.loaded_plugins.append(plugin)
        logging.info(f"Finished loading plugin: {plugin.name}")

    def _load_detection_module(self, plugin: DetectionModule):
        pass

    def _load_default_enabled(self):
        logging.info("Loading installed analysis modules that are enabled by default")
        for plugin_name in PluginDiscovery().get_plugins(default_enabled=True):
            plugin = PluginDiscovery().build_plugin(plugin_name)
            self.load(plugin)
