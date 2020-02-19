from mythril.plugin import MythrilPluginLoader, MythrilPlugin
from mythril.plugin.loader import UnsupportedPluginType

import pytest


def test_typecheck_load():
    # Arrange
    loader = MythrilPluginLoader()

    # Act
    with pytest.raises(ValueError):
        loader.load(None)


def test_unsupported_plugin_type():
    # Arrange
    loader = MythrilPluginLoader()

    # Act
    with pytest.raises(UnsupportedPluginType):
        loader.load(MythrilPlugin())
