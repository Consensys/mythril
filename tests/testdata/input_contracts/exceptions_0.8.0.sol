pragma solidity ^0.8.0;


contract Exceptions {

    uint val;

    function change_val() public {
        val = 1;
    }
    function assert1() public pure {
    	uint256 i = 1;
        assert(i == 0);
    }

    function fail() public view {
        assert(val==2);
    }


}
