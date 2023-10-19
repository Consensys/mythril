pragma solidity ^0.8.0;

contract Regression_1 {
    mapping (address => uint256) private userBalances;

    uint256 public constant TOKEN_PRICE = 1 ether;
    string public constant name = "Moon Token";
    string public constant symbol = "MOON";

    // The token is non-divisible
    // You can buy/sell/transfer 1, 2, 3, or 46 tokens but not 33.5
    uint8 public constant decimals = 0;

    uint256 public totalSupply;

    function buy(uint256 _amount) external payable {
        require(
            msg.value == _amount * TOKEN_PRICE, 
            "Ether submitted and Token amount to buy mismatch"
        );

        userBalances[msg.sender] += _amount;
        totalSupply += _amount;
    }

    function sell(uint256 _amount) external {
        require(userBalances[msg.sender] >= _amount, "Insufficient balance");

        userBalances[msg.sender] -= _amount;
        totalSupply -= _amount;

        (bool success, ) = msg.sender.call{value: _amount * TOKEN_PRICE}("");
        require(success, "Failed to send Ether");

        assert(getEtherBalance() == totalSupply * TOKEN_PRICE);
    }

    function transfer(address _to, uint256 _amount) external {
        require(_to != address(0), "_to address is not valid");
        require(userBalances[msg.sender] >= _amount, "Insufficient balance");
        
        userBalances[msg.sender] -= _amount;
        userBalances[_to] += _amount;
    }

    function getEtherBalance() public view returns (uint256) {
        return address(this).balance;
    }

    function getUserBalance(address _user) external view returns (uint256) {
        return userBalances[_user];
    }
}