pragma solidity ^0.8.0;

contract Test {
    uint256 immutable inputSize;

    constructor(uint256 _log2Size) {
        inputSize = (1 << _log2Size);
    }

    function getBytes(bytes calldata _input) public view returns (bytes32) {
        require(
            _input.length > 0 && _input.length <= inputSize,
            "input len: (0,inputSize]"
        );

        return "123";
    }

    function commencekilling() public {
        address payable receiver = payable(msg.sender);
	selfdestruct(receiver);
    }
}
