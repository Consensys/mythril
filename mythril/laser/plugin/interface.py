from mythril.laser.ethereum.svm import LaserEVM


class LaserPlugin:
    """Base class for laser plugins

    Functionality in laser that the symbolic execution process does not need to depend on
    can be implemented in the form of a laser plugin.

    Laser plugins implement the function initialize(symbolic_vm) which is called with the laser virtual machine
    when they are loaded.
    Regularly a plugin will introduce several hooks into laser in this function

    Plugins can direct actions by raising Signals defined in mythril.laser.ethereum.plugins.signals
    For example, a pruning plugin might raise the PluginSkipWorldState signal.
    """

    def initialize(self, symbolic_vm: LaserEVM) -> None:
        """Initializes this plugin on the symbolic virtual machine

        :param symbolic_vm: symbolic virtual machine to initialize the laser plugin on
        """
        raise NotImplementedError
