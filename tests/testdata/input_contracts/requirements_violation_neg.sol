pragma solidity ^0.4.25;

contract Bar {
    Foo private f = new Foo();
    function doubleBaz() public view returns (int256) {
        return 2 * f.baz(1); //Changes the external contract to not hit the overly strong requirement.
    }
}

contract Foo {
    function baz(int256 x) public pure returns (int256) {
        require(0 < x); //You can also fix the contract by changing the input to the uint type and removing the require
        return 42;
    }
}