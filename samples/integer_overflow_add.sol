pragma solidity ^0.4.18;

contract Token {

  uint public withdrawMax = 10000000000000;
  uint bonus = 1000000000;

  function withdraw(uint amount) public returns (uint) {

    if ((amount + bonus) < withdrawMax) {
        msg.sender.transfer(amount);
    }

  }

}