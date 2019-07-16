

contract Crowdfunding {

  mapping(address => uint) public balances;
  address public owner;
  uint256 INVEST_MIN = 1 ether;
  uint256 INVEST_MAX = 10 ether;

  modifier onlyOwner() {
    require(msg.sender == owner);
    _;
  }

  function crowdfunding() public {
    owner = msg.sender;
  }

  function withdrawfunds() public onlyOwner {
    msg.sender.transfer(address(this).balance);
  }

  function invest() public payable {
    require(msg.value > INVEST_MIN && msg.value < INVEST_MAX);

    balances[msg.sender] += msg.value;
  }

  function getBalance() public view returns (uint) {
    return balances[msg.sender];
  }

}
