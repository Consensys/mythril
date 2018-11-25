pragma solidity 0.5.0;


contract D {
    uint public n;
    address public sender;

    function callSetN(address _e, uint _n) public {
        _e.call(abi.encode(bytes4(keccak256("setN(uint256)")), _n));
    }

    function callcodeSetN(address _e, uint _n) public {
        _e.staticcall(abi.encode(bytes4(keccak256("setN(uint256)")), _n));
    }

    function delegatecallSetN(address _e, uint _n) public {
        _e.delegatecall(abi.encode(bytes4(keccak256("setN(uint256)")), _n));
    }
}
