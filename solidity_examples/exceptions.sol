

contract Exceptions {

    uint256[8] myarray;

    function assert1() public pure {
    	uint256 i = 1;
        assert(i == 0);
    }

    function assert2() public pure {
    	uint256 i = 1;
        assert(i > 0);
    }

    function assert3(uint256 input) public pure {
        assert(input != 23);
    }

    function requireisfine(uint256 input) public pure {
        require(input != 23);
    }

    function divisionby0(uint256 input) public pure {
        uint256 i = 1/input;
    }

    function thisisfine(uint256 input) public pure {
        if (input > 0) {
            uint256 i = 1/input;
        }
    }

    function arrayaccess(uint256 index) public view {
        uint256 i = myarray[index];
    }

    function thisisalsofind(uint256 index) public view {
        if (index < 8) {
            uint256 i = myarray[index];
        }
    }

}
