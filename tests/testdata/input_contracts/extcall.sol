pragma solidity ^0.6.0;

interface IERC20 {
    function transfer(address to, uint256 amount) external returns (bool);
}

contract A {
    constructor() public {
        /// nothing detected
        address(0).call("");
        IERC20(address(0)).transfer(address(0), 0);
        assert(false);
    }
}

