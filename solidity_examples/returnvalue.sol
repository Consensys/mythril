contract ReturnValue {

  address callee = 0xE0F7e56e62b4267062172495D7506087205A4229;

  function call1() returns (uint256) {
    callee.call();
  }

  function call2() returns (uint256) {

    
  }

  function call3() returns (uint256) {

    
  }

}