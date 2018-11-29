pragma solidity 0.5.0;


contract Caller {

    //Just some useless variables
    address public fixedAddress;
    address public storedAddress;

    //useless (but good for testing as they contribute as decoys)
    uint256 private statevar;
    bytes32 private far;

    constructor (address addr) public {
        fixedAddress = addr;
    }

    //some typical function as a decoy
    function thisisfine() public {
        (bool success, bytes memory mem) = fixedAddress.call("");
    }

    function sha256Test1() public returns (uint256) {
        uint256 i;
        if (sha256(abi.encodePacked("ab", "c")) == sha256("abc")) {
            // True
            i = 5555555555555555;
        } else {
            // False
            i = 323232325445454546;
        }
        return i;
    }

    function sha256Test2() public returns (uint256) {
        uint256 i;
        if (sha256("abd") == sha256(abi.encodePacked("ab", "d"))) {
            // True
            i = 34756834765834658;
        } else {
            // False
            i = 8756476956956795876987;
        }
        return i;
    }

     function ripemdTest() public returns (uint256) {
         uint256 i;
         bytes20 v1 = ripemd160("");
         bytes20 v2 = ripemd160("hhhhh");

         if (v1 != v2) {
             // True
             i = 999999999999999999993;
         } else {
             // False
             i = 1111111111112;
         }
         return i;
     }

    function ecrecoverTest() public returns (uint256) {
        bytes32 foobar1 = 0x1c8aff950685c2ed4bc3174f3472287b56d9517b9c948127319a09a7a36deac8;
        bytes32 foobar2 = 0x38d18acb67d25c8bb9942764b62f18e17054f66a817bd4295423adf9ed98873e;
        uint8 v = 28;
        bytes32 r = 0x9242685bf161793cc25603c231bc2f568eb630ea16aa137d2664ac8038825608;
        bytes32 s = 0x4f8ae3bd7535248d0bd448298cc2e2071e56992d0774dc340c368ae950852ada;
        uint256 i;
        address addr1 = ecrecover(keccak256(abi.encodePacked(foobar1)), v, r, s);
        address addr2 = ecrecover(keccak256(abi.encodePacked(foobar1, foobar2)), v, r, s);
        if (addr1 != addr2) {
            // True
            i = 674837568743979857398564869;
        } else {
            // False
            i = 3487683476979311;
        }
        return i;
    }

    //identity is invoked here in compiler and not below
    function needIdentityInvoke(uint sea) public returns (uint) {
        return sea;
    }

    function identityFunction(int input) public returns(int out) {
        assembly {
            let x := mload(0x40)
            mstore(x, input)

            let success := call(500000000, 0x4, 100000, x, 0x20, x, 0x20)
            out := mload(x)
            mstore(0x40, x)
        }
    }

    function identityTest1() public returns (uint256) {
        uint256 i;
        if (identityFunction(100) == 100) {
            // True
            i = 87426857369875698;
        } else {
            // False
            i = 476934798798347;
        }
        return i;
    }
}
