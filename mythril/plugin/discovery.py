import pkg_resources
from mythril.support.support_utils import Singleton
from mythril.plugin.interface import MythrilPlugin

from typing import List


class PluginDiscovery(object, metaclass=Singleton):
    """PluginDiscovery class

     This plugin implements the logic to discover and build plugins in installed python packages
    """

    # Installed plugins structure. Retrieves all modules that have an entry point for mythril.plugins
    _installed_plugins = {
        entry_point.name: entry_point.load()
        for entry_point in pkg_resources.iter_entry_points("mythril.plugins")
    }

    def is_installed(self, plugin_name: str) -> bool:
        """Returns whether there is python package with a plugin with plugin_name"""
        return plugin_name in self._installed_plugins.keys()

    def build_plugin(self, plugin_name: str) -> MythrilPlugin:
        """Returns the plugin for the given plugin_name  if it is installed"""
        if not self.is_installed(plugin_name):
            raise ValueError(f"Plugin with name: `{plugin_name}` is not installed")

        plugin = self._installed_plugins.get(plugin_name)

        if plugin is None or not issubclass(plugin, MythrilPlugin):
            raise ValueError(f"No valid plugin was found for {plugin_name}")

        return plugin()

    def get_plugins(self, default_enabled=None) -> List[str]:
        """ Gets a list of installed mythril plugins

        :param default_enabled: Select plugins that are enabled by default
        :return: List of plugin names
        """
        if default_enabled is None:
            return list(self._installed_plugins.keys())

        return [
            plugin_name
            for plugin_name, plugin_class in self._installed_plugins.items()
            if plugin_class.plugin_default_enabled == default_enabled
        ]
