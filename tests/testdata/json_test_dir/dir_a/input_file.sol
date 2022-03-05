import "@openzeppelin/contracts/token/PRC20/PRC20.sol";

contract Nothing is PRC20{
	string x_0 = "";

	bytes3 x_1 = "A";

	bytes5 x_2 = "E";

	bytes5 x_3 = "";

	bytes3 x_4 = "I";

	bytes3 x_5 = "U";

	bytes3 x_6 = "O";

	bytes3 x_7 = "0";

	bytes3 x_8 = "U";

	bytes3 x_9 = "U";
	function stringCompare(string memory a, string memory b) internal pure returns (bool) {
		if(bytes(a).length != bytes(b).length) {
			return false;
		} else {
			return keccak256(bytes(a)) == keccak256(bytes(b));
		}
	}

    function nothing(string memory g_0, bytes3 g_1, bytes5 g_2, bytes5 g_3, bytes3 g_4, bytes3 g_5, bytes3 g_6, bytes3 g_7, bytes3 g_8, bytes3 g_9, bytes3 g_10, bytes3 g_11) public view returns (bool){
        if (!stringCompare(g_0, x_0)) return false;
				
		if (g_1 != x_1) return false;
				
		if (g_2 != x_2) return false;
				
		if (g_3 != x_3) return false;
				
		if (g_4 != x_4) return false;
				
		if (g_5 != x_5) return false;
				
		if (g_6 != x_6) return false;
				
		if (g_7 != x_7) return false;
				
		if (g_8 != x_8) return false;
				
		if (g_9 != x_9) return false;
		
        if (g_10 != x_9) return false;

        if (g_11 != x_9) return false;

		return true;

    }
}

