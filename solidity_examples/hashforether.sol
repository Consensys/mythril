pragma solidity 0.5.0;


contract HashForEther {

    function withdrawWinnings() public payable {
        // Winner if the last 8 hex characters of the address are 0.
        if (uint32(msg.sender) == 0)
            _sendWinnings();
    }

    function _sendWinnings() public {
        msg.sender.transfer(address(this).balance);
    }
}
