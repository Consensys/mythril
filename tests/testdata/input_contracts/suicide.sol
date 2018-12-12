

contract Suicide {

  function kill(address payable addr) public {
    selfdestruct(addr);
  }

}
