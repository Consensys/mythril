pragma solidity ^0.4.18;

contract Token {

  uint public withdrawMax = 10000000000000;

  function withdraw(uint amount) public returns (uint) {

    if ((amount * 1 ether) > withdrawMax) {
    	throw;
    }
    
    msg.sender.transfer(amount);

  }

}