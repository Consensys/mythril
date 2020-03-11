from mythril.laser.plugin.interface import LaserPlugin

from abc import ABC, abstractmethod
from typing import Optional


class PluginBuilder(ABC):
    """ PluginBuilder

    The plugin builder interface enables construction of Laser plugins
    """

    plugin_name = "Default Plugin Name"

    @abstractmethod
    @property
    def enabled(self) -> Optional[bool]:
        """Returns whether this plugin builder is enabled"""
        pass

    @abstractmethod
    def __call__(self, *args, **kwargs) -> LaserPlugin:
        """Constructs the plugin"""
        pass
