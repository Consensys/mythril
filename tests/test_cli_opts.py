from mythril.interfaces.cli import main
import pytest
import json

import sys

def test_version_opt(capsys):
    # Check that "myth --version" returns a string with the word
    # "version" in it
    sys.argv = ['mythril', '--version']
    with pytest.raises(SystemExit) as pytest_wrapped_e:
        main()
    assert pytest_wrapped_e.type == SystemExit
    captured = capsys.readouterr()
    assert captured.out.find(' version ') >= 1

    # Check that "myth --version -o json" returns a JSON object
    sys.argv = ['mythril', '--version', '-o', 'json']
    with pytest.raises(SystemExit) as pytest_wrapped_e:
        main()
    assert pytest_wrapped_e.type == SystemExit
    captured = capsys.readouterr()
    d = json.loads(captured.out)
    assert isinstance(d, dict)
    assert d['version_str']
