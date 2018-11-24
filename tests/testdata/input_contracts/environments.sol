pragma solidity 0.5.0;


contract IntegerOverflow2 {
    uint256 public count = 7;
    mapping(address => uint256) balances;

  function batchTransfer(address[] _receivers, uint256 _value) public returns(bool){
    uint cnt = _receivers.length;
    uint256 amount = uint256(cnt) * _value;

    require(cnt > 0 && cnt <= 20);

    balances[msg.sender] -=amount;

    return true;
  }

}
