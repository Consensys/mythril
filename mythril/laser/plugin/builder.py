from mythril.laser.plugin.interface import LaserPlugin

from abc import ABC, abstractmethod
from typing import Optional


class PluginBuilder(ABC):
    """ PluginBuilder

    The plugin builder interface enables construction of Laser plugins
    """

    plugin_name = "Default Plugin Name"

    def __init__(self):
        self.enabled = True

    @abstractmethod
    def __call__(self, *args, **kwargs) -> LaserPlugin:
        """Constructs the plugin"""
        pass
