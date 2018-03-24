pragma solidity ^0.4.17;

contract Transfer1 {

  function transfer() {
    msg.sender.transfer(1 ether);
  }

}

contract Transfer2 {

  function transfer() {
    msg.sender.transfer(2 ether);
  }

}
