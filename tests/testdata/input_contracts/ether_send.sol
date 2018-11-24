pragma solidity 0.5.0;


contract Crowdfunding {

  mapping(address => uint) public balances;
  address public owner;
  uint256 INVEST_MIN = 1 ether;
  uint256 INVEST_MAX = 10 ether;

  modifier onlyOwner() {
    require(msg.sender == owner);
    _;
  }

  function crowdfunding() {
    owner = msg.sender;
  }

  function withdrawfunds() onlyOwner {
    msg.sender.transfer(this.balance);
  }

  function invest() public payable {
    require(msg.value > INVEST_MIN && msg.value < INVEST_MAX);

    balances[msg.sender] += msg.value;
  }

  function getBalance() public constant returns (uint) {
    return balances[msg.sender];
  }

}
