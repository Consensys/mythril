pragma solidity ^0.8.0;

contract BasicLiquidation {
    bool[4096] _flags;
    constructor() payable
    {
        require(msg.value == 0.1 ether);
        _flags[1234] = true;
    }
    function extractMoney(uint256 idx) public payable
    {
        require(idx >= 0);
        require(idx < 4096);
        require(_flags[idx]);
        payable(msg.sender).transfer(address(this).balance);
    }
}