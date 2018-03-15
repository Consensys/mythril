pragma solidity ^0.4.17;

contract Callee {
    function theFunction() payable {
    }
}

contract Caller {

	address public fixed_address;
	address public stored_address;

	function Caller(address addr) {
		fixed_address = addr;
	}

	function thisisfine() public {
	    Callee(fixed_address).theFunction();
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