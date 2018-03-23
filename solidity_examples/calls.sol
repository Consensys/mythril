pragma solidity ^0.4.17;


contract Caller {

	address public fixed_address;
	address public stored_address;

	uint256 statevar;

	function Caller(address addr) {
		fixed_address = addr;
	}

	function thisisfine() public {
	    fixed_address.call();
	}

	function reentrancy() public {
	    fixed_address.call();
	    statevar = 0;
	}
	
	function calluseraddress(address addr) {
	    addr.call();
	}

	function callstoredaddress() {
	    stored_address.call();
	}	
	
	function setstoredaddress(address addr) {
	    stored_address = addr;
	}	
	
}