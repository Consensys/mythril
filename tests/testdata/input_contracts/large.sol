contract B{
    uint x=0;
    uint total=0;
    function incr() public returns(uint){
        x += 1;
    }


    function foo() public returns(uint){
        require(x==10);
        selfdestruct(msg.sender);
    }
}

