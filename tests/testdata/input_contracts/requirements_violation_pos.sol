pragma solidity ^0.4.25;

contract Bar {
    Foo private f = new Foo();
    function doubleBaz() public view returns (int256) {
        return 2 * f.baz(0);
    }
}

contract Foo {
    function baz(int256 x) public pure returns (int256) {
        require(0 < x);
        return 42;
    }
}