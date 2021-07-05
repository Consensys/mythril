pragma solidity 0.8.6;

/**
 * @title Storage
 * @dev Store & retreive value in a variable
 */
contract D1 {

    uint256 number;

    function store(uint256 num) public {
        assert(num < 5);
        number =num;
    }
    
    function retval() public returns(uint256){
        return number;
    }
}

contract D2 {
 D1 d1;
  constructor() public
  {
       d1 = D1(0x0901d12ebE1b195E5AA8748E62Bd7734aE19B51F);
  }
  function test(uint256 num) public returns(uint256) {
    uint256 sum = d1.retval() + num;
    if (sum == 10) {
        return sum + 10;
    }
    else if(sum == 11) {
        return sum + 12;
    }
    else if(sum == 30) {
        return sum * 2;
    }
    assert(sum != 20);
    return sum;
  }
}

