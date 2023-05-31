import pytest

from mythril.ethereum.util import extract_version


test_data = (
    ("pragma solidity 0.5.0\n", ["0.5.0"]),
    ("pragma solidity ^0.4.26\n", ["0.4.26"]),
    ("pragma solidity ^0.6.3;\n", [f"0.6.{x}" for x in range(3, 13)]),
    ("pragma solidity ^0.6.3              ;\n", [f"0.6.{x}" for x in range(3, 13)]),
    (
        "pragma solidity ^0.6.3;                       \n",
        [f"0.6.{x}" for x in range(3, 13)],
    ),
    (
        "pragma solidity ^0.6.3       ;                       \n",
        [f"0.6.{x}" for x in range(3, 13)],
    ),
    (
        """pragma solidity >=0.4.0 <0.6.0             ;               
        contract SimpleStorage {
            uint storedData;
            function set(uint x) public {
                storedData = x;
            }
            function get() public view returns (uint) {
                return storedData;
            }
        }""",
        [f"0.4.{x}" for x in range(11, 27)] + [f"0.5.{x}" for x in range(0, 18)],
    ),
    (
        """
        pragma solidity >=0.4.0 <0.6.0
        ;contract SimpleStorage {
            uint storedData;
            function set(uint x) public {
                storedData = x;
            }
            function get() public view returns (uint) {
                return storedData;
            }
        }""",
        [f"0.4.{x}" for x in range(11, 27)] + [f"0.5.{x}" for x in range(0, 18)],
    ),
    (
        """
        pragma solidity >=0.4.0 <0.6.0
        ;contract SimpleStorage {
            uint storedData;
            function set(uint x) public {
                storedData = x;
            }
            function get() public view returns (uint) {
                return storedData;
            }
        }""",
        [f"0.4.{x}" for x in range(11, 27)] + [f"0.5.{x}" for x in range(0, 18)],
    ),
    (
        """
        pragma solidity >= 0.5.0 < 0.6.0;
        ;contract SimpleStorage {
            uint storedData;
            function set(uint x) public {
                storedData = x;
            }
            function get() public view returns (uint) {
                return storedData;
            }
        }""",
        [f"0.5.{x}" for x in range(0, 18)],
    ),
    (
        """
        pragma solidity   >=   0  .  4  .0 <  0  .  6  .         0
        ;contract SimpleStorage {
            uint storedData;
            function set(uint x) public {
                storedData = x;
            }
            function get() public view returns (uint) {
                return storedData;
            }
        }""",
        [f"0.4.{x}" for x in range(11, 27)] + [f"0.5.{x}" for x in range(0, 18)],
    ),
)


@pytest.mark.parametrize("input_,output", test_data)
def test_sar(input_, output):
    assert extract_version(input_) in output
