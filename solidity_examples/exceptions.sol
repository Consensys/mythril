pragma solidity 0.5.0;


contract Exceptions {

    uint256[8] myarray;

    function assert1() public {
    	uint256 i = 1;
        assert(i == 0);
    }

    function assert2() public {
    	uint256 i = 1;
        assert(i > 0);
    }

    function assert3(uint256 input) public {
        assert(input != 23);
    }

    function requireisfine(uint256 input) public {
        require(input != 23);
    }

    function divisionby0(uint256 input) public {
        uint256 i = 1/input;
    }

    function thisisfine(uint256 input) public {
        if (input > 0) {
            uint256 i = 1/input;
        }
    }

    function arrayaccess(uint256 index) public {
        uint256 i = myarray[index];
    }

    function thisisalsofind(uint256 index) public {
        if (index < 8) {
            uint256 i = myarray[index];
        }
    }

}
