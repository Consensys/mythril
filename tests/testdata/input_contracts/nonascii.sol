pragma solidity 0.5.0;


contract nonAscii {
  function renderNonAscii () public pure returns (string memory) {
	  return "Хэллоу Ворлд";
  }
}