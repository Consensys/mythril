

contract AssertFail {
    constructor(uint8 var1) public {
        assert(var1 > 0);
    }
}
