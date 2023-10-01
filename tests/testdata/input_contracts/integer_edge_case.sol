// SPDX-License-Identifier: MIT
pragma solidity ^0.8.19;
contract B {
    function f(uint256 arg) public view returns(uint256) {
        uint256 res;
        unchecked{        
            res = 10_000_000_000 * arg; // undetected overflow
        }
        //assert(res > arg); // the assertion violation is correctly detected if added
        return res;       
    }
}
