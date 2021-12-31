class PluginSignal(Exception):
    """Base plugin signal

    These signals are used by the laser plugins to create intent for certain actions in the symbolic virtual machine
    """

    pass


class PluginSkipWorldState(PluginSignal):
    """Plugin to skip world state

    Plugins that raise this signal while the add_world_state hook is being executed
    will force laser to abandon that world state.
    """

    pass


class PluginSkipState(PluginSignal):
    """Plugin to skip world state

    Plugins that raise this signal while the add_world_state hook is being executed
    will force laser to abandon that world state.
    """

    pass
