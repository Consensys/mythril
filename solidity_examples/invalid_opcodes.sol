contract InvalidOpcodes {
    
    function assert1() {
    	uint256 i = 1;
        assert(i == 0);
    }

    function assert2() {
    	uint256 i = 1;
        assert(i > 0);
    }

    function assert3(uint input) {
        assert(input != 23);
    }
}
