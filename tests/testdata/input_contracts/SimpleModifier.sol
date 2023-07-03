pragma solidity ^0.5.0;



contract SimpleModifier {

  address payable public owner;

  modifier onlyOwner() {
    require(msg.sender == owner);
    _;
  }


  function withdrawfunds() public onlyOwner {
    owner.send(address(this).balance);
  }

}
