contract Suicide {

  function kill(address addr) {
    selfdestruct(addr);
  }

}