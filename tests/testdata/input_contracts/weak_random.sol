pragma solidity 0.5.0;


contract WeakRandom {
    struct Contestant {
        address addr;
        uint gameId;
    }

    uint public constant prize = 2.5 ether;
    uint public constant totalTickets = 50;
    uint public constant pricePerTicket = prize / totalTickets;

    uint public gameId = 1;
    uint public nextTicket = 0;
    mapping (uint => Contestant) public contestants;

    function () payable public {
        uint moneySent = msg.value;

        while (moneySent >= pricePerTicket && nextTicket < totalTickets) {
            uint currTicket = nextTicket++;
            contestants[currTicket] = Contestant(msg.sender, gameId);
            moneySent -= pricePerTicket;
        }

        if (nextTicket == totalTickets) {
            chooseWinner();
        }

        // Send back leftover money
        if (moneySent > 0) {
            msg.sender.transfer(moneySent);
        }
    }

    function chooseWinner() private {
        address seed1 = contestants[uint(block.coinbase) % totalTickets].addr;
        address seed2 = contestants[uint(msg.sender) % totalTickets].addr;
        uint seed3 = block.difficulty;
        bytes32 randHash = keccak256(seed1, seed2, seed3);

        uint winningNumber = uint(randHash) % totalTickets;
        address winningAddress = contestants[winningNumber].addr;

        gameId++;
        nextTicket = 0;
        winningAddress.transfer(prize);
    }
}
