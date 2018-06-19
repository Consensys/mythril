pragma solidity ^0.4.17;


contract Caller {

    address public fixed_address;  //Just some useless variables
    address public stored_address;  

    uint256 statevar;        //useless( but good for testing as they contribute as decoys)
    bytes32 far;

    function Caller(address addr) { 
        fixed_address = addr;
    }

    function thisisfine() public {      //some typical function as a decoy
        fixed_address.call();
    }
    function sha256_test1() public {
        uint256 i;
        if(sha256('ab','c') == 0xba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad){    //True
            i = 5555555555555555;
        }

        if(sha256('abc') == 0xba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad){      //True
            i = 323232325445454546;
        }
    }
    function sha256_test2() public {
        uint256 i;
        if(sha256('abd') == 0xba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad) {     //False
            i = 34756834765834658;
        }
        if(sha256('ab','d') == 0xa52d159f262b2c6ddb724a61840befc36eb30c88877a4030b65cbe86298449c9) {  //True
            i = 8756476956956795876987;
        }
    }
    function sha256_test3() public {
        uint256 i;
        if(sha256('') == 0xe3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855) {         //True
            i = 5763467587689578369;
        }
        if(sha256('hhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhfdhhfdhhhhhh') == 0xe4ebd771f821e3277b77dcc39e94fe7172a5c9c8c12f8885c2d5513385a0a8b8) {  //False
            i = 948365957658767467857;
        }
    }

    function ripemd_test1() public {
        uint256 i;
        if(ripemd160('ab','c') == 0x8eb208f7e05d987a9b044a8e98c6b087f15a0bfc){    //True
            i = 1242435356364;
        }
        if(ripemd160('abc') == 0x8eb208f7e05d987a9b044a8e98c6b087f15a0bfc){      //True
            i = 6732648654386435;
        }
    }
    function ripemd_test2() public {
        uint256 i;
        if(ripemd160('abd') == 0x8eb208f7e05d987a9b044a8e98c6b087f15a0bfc) {     //False
            i = 97457657536546465;
        }
        if(ripemd160('ab','d') == 0xb0a79cc77e333ea11974e105cd051d33836928b0) {  //True
            i = 56436346436456546;
        }
    }
    function ripemd_test3() public {
        uint256 i;
        if(ripemd160('') == 0x9c1185a5c5e9fc54612808977ee8f548b2258d31) {         //True
            i = 999999999999999999993;
        }
        if(ripemd160('hhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhh') == 0x2d1b88a5daa5d138eb7bb14ee320010937f0ebe7) {  //False
            i = 1111111111112;
        }
    }

    function ecrecover_test1() public {
        bytes32 foobar = 0x1c8aff950685c2ed4bc3174f3472287b56d9517b9c948127319a09a7a36deac8;
        bytes memory prefix = "\x19Ethereum Signed Message:\n32";
        bytes32 prefixedHash = keccak256(prefix, foobar);
        uint8 v = 28;
        bytes32 r = 0x9242685bf161793cc25603c231bc2f568eb630ea16aa137d2664ac8038825608;
        bytes32 s = 0x4f8ae3bd7535248d0bd448298cc2e2071e56992d0774dc340c368ae950852ada;
        if( ecrecover(prefixedHash, v, r, s) == 0x7156526fbd7a3c72969b54f64e42c10fbb768c8a)   {  //True
            uint256 bignum = 786428768768632537676;
        }
        if( ecrecover(prefixedHash, v, r, s) == 0x7156526fbd7a3c72969b54f64e42c10fbb768c8b) {   //False
            uint256 small = 4897983476979346779638;
        }
        foobar = 0x38d18acb67d25c8bb9942764b62f18e17054f66a817bd4295423adf9ed98873e;
        if( ecrecover( keccak256(foobar), v, r, s) == 0x0faf91ea0aaaa5377dfdf188b21409007f0b4019) {    //True
            uint256 dk = 674837568743979857398564869;
        }
        foobar = 0x38d18acb67d25c7bb9942764b62f18e17054f66a817bd4295423adf9ed98873e; //not same as above, minor change(7bb instead of 8bb)
        if( ecrecover( keccak256(foobar), v, r, s) == 0x0faf91ea0aaaa5377dfdf188b21409007f0b4019) {    //False
            uint256 pk = 3487683476979311;
        }

    }

    function ecrecover_test2() public {
        bytes32 foobar = 0x1c8aff950685c2ed4bc3174f3472287b56d9517b9c948127319a09a7a36deac8;
        bytes memory prefix = "\x19Ethereum Signed Message:\n32";
        bytes32 prefixedHash = keccak256(prefix, foobar);
        uint8 v = 26;
        bytes32 r = 0x9242685bf161793cc25603c231bc2f568eb630ea16aa137d2664ac8038825608;
        bytes32 s = 0x4f8ae3bd7535248d0bd448298cc2e2071e56992d0774dc340c368ae950852ada;
        if( ecrecover(prefixedHash, v, r, s) == 0x0000000000000000000000000000000000000000)   {   //True
            uint256 bignum = 853729594875984769847369;
        }
        if( ecrecover(prefixedHash, v, r, s) == 0x7156526fbd7a3c72969b54f64e42c10fbb768c8b) {     //False
            uint256 small = 83579382475972439587;
        }
    }
    function ecrecover_test3() public {
        bytes32 foobar = 0x1c8aff950685c2ed4bc3174f3472287b56d9517b9c948127319a09a7a36deac8;
        bytes memory prefix = "\x19Ethereum Signed Message:\n32";
        bytes32 prefixedHash = keccak256(prefix, foobar);
        uint8 v = 29;
        bytes32 r = 0x9242685bf161793cc25603c231bc2f568eb630ea16aa137d2664ac8038825608;
        bytes32 s = 0x4f8ae3bd7535248d0bd448298cc2e2071e56992d0774dc340c368ae950852ada;
        if( ecrecover(prefixedHash, v, r, s) == 0x0000000000000000000000000000000000000000)   {   //True
            uint256 bignum = 8437589437695876985769;
        }
        if( ecrecover(prefixedHash, v, r, s) == 0x7156526fbd7a3c72969b54f64e42c10fbb768c8b) {     //False
            uint256 small = 9486794873598347697596;
        }
    }
    function ecrecover_test4() public {
        bytes32 foobar = 0x1c8aff950685c2ed4bc3174f3472287b56d9517b9c948127319a09a7a36deac8;
        bytes memory prefix = "\x19Ethereum Signed Message:\n32";
        bytes32 prefixedHash = keccak256(prefix, foobar);
        uint8 v = 27;
        bytes32 r = 0xfffffffffffffffffffffffffffffffffaaedce6af48a03bbfd25e8cd0364141;  //greater than the max limit
        bytes32 s = 0x4f8ae3bd7535248d0bd448298cc2e2071e56992d0774dc340c368ae950852ada;

        if( ecrecover(prefixedHash, v, r, s) == 0x0000000000000000000000000000000000000000)   {   //True
            uint256 bignum = 346934876983476;
        }
    }
    function need_identity_invoke(uint sea) returns (uint) {
        return sea;                                     //identity is invoked here in compiler and not below
    }
    function identity_function(int input) public returns(int out) {
        assembly{
            let x := mload(0x40)
            mstore(x, input)

            let success := call(500000000, 0x4, 100000, x, 0x20, x, 0x20)
            out := mload(x)
            mstore(0x40, x)
        }
    }
    function identity_test1() public{
        if(identity_function(100)==100)         //True
            uint256 smallnum = 87426857369875698;
        if(identity_function(200)==100)         //False
            uint256 bignum = 476934798798347;
    }
    function identity_test2() public{
        if(identity_function(12345678)==12345678)         //True
            uint256 smallnum = 7346948379483769;
        if(identity_function(74648796976)==4685987)         //False
            uint256 bignum = 83269476937987;
    }

}
