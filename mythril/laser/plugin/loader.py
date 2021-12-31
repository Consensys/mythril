import logging
from typing import Dict, List, Optional

from mythril.laser.ethereum.svm import LaserEVM
from mythril.laser.plugin.builder import PluginBuilder
from mythril.support.support_utils import Singleton

log = logging.getLogger(__name__)


class LaserPluginLoader(object, metaclass=Singleton):
    """
    The LaserPluginLoader is used to abstract the logic relating to plugins.
    Components outside of laser thus don't have to be aware of the interface that plugins provide
    """

    def __init__(self) -> None:
        """Initializes the plugin loader"""
        self.laser_plugin_builders = {}  # type: Dict[str, PluginBuilder]
        self.plugin_args = {}  # type: Dict[str, Dict]

    def add_args(self, plugin_name, **kwargs):
        self.plugin_args[plugin_name] = kwargs

    def load(self, plugin_builder: PluginBuilder) -> None:
        """Enables a Laser Plugin

        :param plugin_builder: Builder that constructs the plugin
        """
        log.info(f"Loading laser plugin: {plugin_builder.name}")
        if plugin_builder.name in self.laser_plugin_builders:
            log.warning(
                f"Laser plugin with name {plugin_builder.name} was already loaded, skipping..."
            )
            return
        self.laser_plugin_builders[plugin_builder.name] = plugin_builder

    def is_enabled(self, plugin_name: str) -> bool:
        """Returns whether the plugin is loaded in the symbolic_vm

        :param plugin_name: Name of the plugin to check
        """
        if plugin_name not in self.laser_plugin_builders:
            return False
        else:
            return self.laser_plugin_builders[plugin_name].enabled

    def enable(self, plugin_name: str):
        if plugin_name not in self.laser_plugin_builders:
            return ValueError(f"Plugin with name: {plugin_name} was not loaded")
        self.laser_plugin_builders[plugin_name].enabled = True

    def instrument_virtual_machine(
        self, symbolic_vm: LaserEVM, with_plugins: Optional[List[str]]
    ):
        """Load enabled plugins into the passed symbolic virtual machine
        :param symbolic_vm: The virtual machine to instrument the plugins with
        :param with_plugins: Override the globally enabled/disabled builders and load all plugins in the list
        """
        for plugin_name, plugin_builder in self.laser_plugin_builders.items():
            enabled = (
                plugin_builder.enabled
                if not with_plugins
                else plugin_name in with_plugins
            )

            if not enabled:
                continue

            log.info(f"Instrumenting symbolic vm with plugin: {plugin_name}")
            plugin = plugin_builder(**self.plugin_args.get(plugin_name, {}))
            plugin.initialize(symbolic_vm)
