from mythril.laser.ethereum.svm import LaserEVM
from mythril.laser.ethereum.plugins.plugin import LaserPlugin


class LaserPluginLoader:
    """
    The LaserPluginLoader is used to abstract the logic relating to plugins.
    Components outside of laser thus don't have to be aware of the interface that plugins provide
    """

    def __init__(self, symbolic_vm: LaserEVM) -> None:
        """ Initializes the plugin loader

        :param symbolic_vm: symbolic virtual machine to load plugins for
        """
        self.symbolic_vm = symbolic_vm
        self.laser_plugins = []

    def load(self, laser_plugin: LaserPlugin) -> None:
        """ Loads the plugin

        :param laser_plugin: plugin that will be loaded in the symbolic virtual machine
        """
        laser_plugin.initialize(self.symbolic_vm)
        self.laser_plugins.append(laser_plugin)

    def is_enabled(self, laser_plugin: LaserPlugin) -> bool:
        """ Returns whether the plugin is loaded in the symbolic_vm

        :param laser_plugin: plugin that will be checked
        """
        return laser_plugin in self.laser_plugins
