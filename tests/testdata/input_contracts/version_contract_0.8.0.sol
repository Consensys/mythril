pragma solidity ^0.8.0;

contract Test {
    uint256 input;
    function add(uint256 a, uint256 b) public {
        input = a + b;
    }
}
