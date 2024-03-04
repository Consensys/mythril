// source of the bytecode, as a reference for the test.
pragma solidity 0.8.6;

contract Example1 {
    uint256 private initialized = 0;
    uint256 public count = 1;

    function init() public {
        initialized = 1;
    }

    function run(uint256 input, uint val) public {
        if (val == 3) {
            count += input;
        }
        else
            count++;
    }
}
