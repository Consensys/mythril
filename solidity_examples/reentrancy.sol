contract Reentrancy {

  mapping(address => uint) public balances;

  function donate(address _to) public payable {
    balances[_to] += msg.value;
  }

  function balanceOf(address _who) public constant returns (uint balance) {
    return balances[_who];
  }

  function withdraw(uint _amount) public {
    if(balances[msg.sender] >= _amount) {
      msg.sender.call.value(_amount)();
      balances[msg.sender] -= _amount;
    }
  }

  function() payable {}
}