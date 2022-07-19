from subprocess import Popen, PIPE
from tests import PROJECT_DIR, TESTDATA
import json

MYTH = str(PROJECT_DIR / "myth")


def test_parallel():

    test_file = str(TESTDATA / "input_contracts" / "origin.sol")
    program = f"python3 {MYTH} a {test_file} --solv 0.5.0 -o json"
    processes = [Popen(program, stdout=PIPE, shell=True) for i in range(30)]
    for p in processes:
        out, err = p.communicate()
        json_output = json.loads(out.decode("utf-8"))
        assert json_output["success"] == True
