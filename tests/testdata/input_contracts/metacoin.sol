pragma solidity ^0.4.17;

contract metaCoin {
	mapping (address => uint) public balances;
	function metaCoin() public {
		balances[msg.sender] = 10000;
	}
	
	function sendToken(address receiver, uint amount) public returns(bool successful){
		if (balances[msg.sender] < amount) return false;
		balances[msg.sender] -= amount;
		balances[receiver] += amount;
		return false;
	}
}
