
contract StorageTest {
      mapping(bytes32 => address) data;

  function confirmAndCheck(uint256 x) public{
      data[keccak256(abi.encodePacked(x))] = msg.sender;
  }

  function destruct(bytes32 x) public{
      require(data[x] == msg.sender);
      selfdestruct(data[x]);
  }

}

