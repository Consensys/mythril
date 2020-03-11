from mythril.laser.ethereum.svm import LaserEVM
from mythril.laser.plugin import LaserPlugin
from typing import Callable, Dict

import logging
from mythril.support.support_utils import Singleton

log = logging.getLogger(__name__)


class LaserPluginLoader(object, metaclass=Singleton):
    """
    The LaserPluginLoader is used to abstract the logic relating to plugins.
    Components outside of laser thus don't have to be aware of the interface that plugins provide
    """

    def __init__(self) -> None:
        """ Initializes the plugin loader """
        self.laser_plugin_builders = {}  # type: Dict[str, Callable[[], LaserPlugin]]

    def enable(
        self, plugin_name: str, plugin_builder: Callable[[], LaserPlugin]
    ) -> None:
        """ Enables a Laser Plugin

        :param plugin_name: Name of the plugin to enable
        :param plugin_builder: Function that builds and returns a laser plugin
        """
        log.info(f"Enabling laser plugin: {plugin_name}")
        if plugin_name in self.laser_plugin_builders:
            log.warning(
                f"Laser plugin with name {plugin_name} was already enabled, skipping..."
            )
            return
        self.laser_plugin_builders[plugin_name] = plugin_builder

    def is_enabled(self, plugin_name: str) -> bool:
        """ Returns whether the plugin is loaded in the symbolic_vm

        :param plugin_name: Name of the plugin to check
        """
        return plugin_name in self.laser_plugin_builders

    def load_plugins(self, symbolic_vm: LaserEVM):
        """ Load enabled plugins into the passed symbolic virtual machine """
        for plugin_name, plugin_builder in self.laser_plugin_builders:
            log.info(f"Instrumenting symbolic vm with plugin: {plugin_name}")
            plugin = plugin_builder()
            plugin.initialize(symbolic_vm)
