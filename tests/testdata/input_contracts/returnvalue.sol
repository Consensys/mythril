pragma solidity 0.5.0;


contract ReturnValue {

  address public callee = 0xE0f7e56E62b4267062172495D7506087205A4229;

  function callnotchecked() public {
    callee.call("");
  }

  function callchecked() public {
    (bool success, bytes memory data) = callee.call("");
    require(success);
  }

}