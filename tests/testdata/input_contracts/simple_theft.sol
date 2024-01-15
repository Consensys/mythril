pragma solidity ^0.8.0;

contract Fallback {

  function withdraw() public { payable(msg.sender).transfer(address(this).balance); }


}
