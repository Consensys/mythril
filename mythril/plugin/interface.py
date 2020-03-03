from abc import ABC, abstractmethod


class MythrilPlugin:
    """MythrilPlugin interface

    Mythril Plugins can be used to extend Mythril in different ways:
    1. Extend Laser, in which case the LaserPlugin interface must also be extended
    2. Extend Laser with a new search strategy in which case the SearchStrategy needs to be implemented
    3. Add an analysis module, in this case the AnalysisModule interface needs to be implemented
    4. Add new commands to the Mythril cli, using the MythrilCLIPlugin Interface
    """

    author = "Default Author"
    name = "Plugin Name"
    plugin_license = "All rights reserved."
    plugin_type = "Mythril Plugin"
    plugin_version = "0.0.1 "
    plugin_description = "This is an example plugin description"

    def __init__(self):
        pass

    def __repr__(self):
        plugin_name = type(self).__name__
        return f"{plugin_name} - {self.plugin_version} - {self.author}"


class MythrilCLIPlugin(MythrilPlugin):
    """MythrilCLIPlugin interface

    This interface should be implemented by mythril plugins that aim to add commands to the mythril cli
    """

    pass
