pragma solidity >= 0   .   5  .   0 < 0  .  6   .  0;

contract Test {
    uint256 input;
    function add(uint256 a, uint256 b) public {
        input = a + b;
    }
}
