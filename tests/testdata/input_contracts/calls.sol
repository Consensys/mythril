pragma solidity 0.5.0;


contract Caller {

	address public fixed_address;
	address public stored_address;

	uint256 statevar;

	constructor(address addr) public {
		fixed_address = addr;
	}

	function thisisfine() public {
	    fixed_address.call("");
	}

	function reentrancy() public {
	    fixed_address.call("");
	    statevar = 0;
	}

	function calluseraddress(address addr) public {
	    addr.call("");
	}

	function callstoredaddress() public {
	    stored_address.call("");
	}

	function setstoredaddress(address addr) public {
	    stored_address = addr;
	}

}