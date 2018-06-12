pragma solidity ^0.4.22;
contract nonAscii {
  function renderNonAscii () public pure returns (string) {
	  return "Хэллоу Ворлд";
  }
}