contract B{
    uint x=0;
    function incr() public returns(uint){
        require(x==0);
        x += 1;
    }
    function incr2() public payable returns(uint){
        require(x==1);
        x += 1;

    }
    function continous_incr() public payable returns(uint){
        require(x>=2);
        x += 1;
    }

    function destroy() public returns(uint){
        selfdestruct(msg.sender);
    }
}

