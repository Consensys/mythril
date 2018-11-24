pragma solidity 0.5.0;


contract MetaCoin {
	mapping (address => uint) public balances;
	function MetaCoin() public {
		balances[msg.sender] = 10000;
	}

	function sendToken(address receiver, uint amount) public returns(bool successful){
		if (balances[msg.sender] < amount) return false;
		balances[msg.sender] -= amount;
		balances[receiver] += amount;
		return false;
	}
}
