pragma solidity 0.5.0;


contract Suicide {

  function kill(address payable addr) public {
    selfdestruct(addr);
  }

}