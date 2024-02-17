pragma solidity ^0.5.0;

contract Lockdrop {

    function lock()
        external
        payable
    {
        uint256 eth = msg.value;
        address owner = msg.sender;
        assert(address(0x0).balance > msg.value);
    }



}