contract B{
    uint x=0;
    uint total = 0;
    function incr() public returns(uint){
        require(x==0);
        x += 1;
    }
    function incr2() public payable returns(uint){
        require(x==1);
        x += 1;
        total += msg.value;
    }
    function continous_incr(uint val) public payable returns(uint){
        require(x>=2);
        x += val;
        total += msg.value;
    }

    function foo() public returns(uint){
        require(x==4);
        x += 1;
        msg.sender.transfer(total);
    }
}

