pragma solidity ^0.4.2;

contract TOY  {

    address public owner;
    bool public FLAG;

    modifier checkOwner {
        require(msg.sender == owner);  _;
    }

    function TOY() { owner = msg.sender; }
    function setFlag(bool newFLAG) public { FLAG = newFLAG;  }
    function boom() public checkOwner {
        selfdestruct(owner);
    }
}
