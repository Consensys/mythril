import pkg_resources
from mythril.support.support_utils import Singleton
from mythril.plugin.interface import MythrilPlugin


class PluginDiscovery(object, metaclass=Singleton):
    """PluginDiscovery class

     This plugin implements the logic to discover and build plugins in installed python packages
    """
    _installed_plugins = {
        entry_point.name: entry_point.load()
        for entry_point
        in pkg_resources.iter_entry_points('mythril.plugins')
    }

    def is_installed(self, plugin_name: str) -> bool:
        return plugin_name in self._installed_plugins.keys()

    def build_plugin(self, plugin_name: str) -> MythrilPlugin:
        if not self.is_installed(plugin_name):
            raise ValueError(f"Plugin with name: `{plugin_name}` is not installed")

        module = self._installed_plugins.get(plugin_name)
        plugin = module.detector

        if plugin is None or not isinstance(plugin, MythrilPlugin):
            raise ValueError(f"No valid plugin was found for {plugin_name}")

        return plugin
