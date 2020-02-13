from mythril.analysis.modules.base import DetectionModule

from mythril.plugin.interface import MythrilCLIPlugin, MythrilPlugin
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
        self.loaded_plugins = []

    def load(self, plugin: MythrilPlugin):
        """Loads the passed plugin"""
        if not isinstance(plugin, MythrilPlugin):
            raise ValueError("Passed plugin is not of type MythrilPlugin")

        log.info(f"Loading plugin: {str(plugin)}")

        if isinstance(plugin, DetectionModule):
            self._load_detection_module(plugin)
        else:
            raise UnsupportedPluginType("Passed plugin type is not yet supported")

        self.loaded_plugins.append(plugin)

    def _load_detection_module(self, plugin: DetectionModule):
        pass
