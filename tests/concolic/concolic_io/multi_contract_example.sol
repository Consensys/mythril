pragma solidity 0.8.6;

/**
 * @title Storage
 * @dev Store & retreive value in a variable
 */
contract D1 {

    uint256 number;

    function store(uint256 num) public {
        number =num;
    }
    
    function retval() public returns(uint256){
        return number;
    }
}
contract D2 {


    uint256 number;

    function store(uint256 num) external {
        number = num;
    }
    function retval() public returns(uint256){
        return number;
    }

}


contract D3 {
 D2 d2;
 D1 d1;
  constructor() public
  {
       d1 = D1(0x0901d12ebE1b195E5AA8748E62Bd7734aE19B51F);
       d2 = D2(0x384f682f4a5AbefC8795Cc38a340dE9446dFAE7A);
  }
  function test(uint256 num) public returns(uint) {
    uint sum = d1.retval() + d2.retval() + num;
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

