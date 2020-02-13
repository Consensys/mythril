from mythril.plugin.interface import MythrilCLIPlugin, MythrilPlugin


def test_construct_cli_plugin():
    _ = MythrilCLIPlugin()


def test_construct_mythril_plugin():
    _ = MythrilPlugin
