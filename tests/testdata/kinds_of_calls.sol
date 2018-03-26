contract D {
    uint public n;
    address public sender;

    function callSetN(address _e, uint _n) {
        _e.call(bytes4(sha3("setN(uint256)")), _n);
    }

    function callcodeSetN(address _e, uint _n) {
        _e.callcode(bytes4(sha3("setN(uint256)")), _n);
    }

    function delegatecallSetN(address _e, uint _n) {
        _e.delegatecall(bytes4(sha3("setN(uint256)")), _n);
    }
}
