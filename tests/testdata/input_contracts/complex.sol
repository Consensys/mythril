
pragma solidity 0.5.0;

contract WalletLibrary {

  struct PendingState {
    uint yetNeeded;
    uint ownersDone;
    uint index;
  }

  struct Transaction {
    address to;
    uint value;
    bytes data;
  }

  modifier onlymanyowners(bytes32 _operation) {
    if (confirmAndCheck(_operation))
      _;
  }


  
  function initMultiowned(address[] memory _owners, uint _required) public only_uninitialized {
    m_numOwners = _owners.length + 1;
    m_owners[1] = uint(msg.sender);
    m_ownerIndex[uint(msg.sender)] = 1;
    for (uint i = 0; i < _owners.length; ++i)
    {
      m_owners[2 + i] = uint(_owners[i]);
      m_ownerIndex[uint(_owners[i])] = 2 + i;
    }
    m_required = _required;
  }

  modifier only_uninitialized { require(m_numOwners == 0); _; }


  function kill(address payable _to) onlymanyowners(keccak256(msg.data)) external {
    selfdestruct(_to);
  }




  function confirmAndCheck(bytes32 _operation) internal returns (bool) {
    uint ownerIndex = m_ownerIndex[uint(msg.sender)];
    if (ownerIndex == 0) return false;

    PendingState memory pending = m_pending[_operation];
    if (pending.yetNeeded == 0) {
      pending.yetNeeded = m_required;
      pending.ownersDone = 0;
      pending.index = m_pendingIndex.length++;
      m_pendingIndex[pending.index] = _operation;
    }
    uint ownerIndexBit = 2**ownerIndex;
    if (pending.ownersDone & ownerIndexBit == 0) {
      if (pending.yetNeeded <= 1) {
        delete m_pendingIndex[m_pending[_operation].index];
        delete m_pending[_operation];
        return true;
      }
      else
      {
        // not enough: record that this owner in particular confirmed.
        pending.yetNeeded--;
        pending.ownersDone |= ownerIndexBit;
      }
    }
    
    
  }


  uint public m_required;
  uint public m_numOwners;


  // list of owners
  uint[256] m_owners;

  mapping(uint => uint) m_ownerIndex;
  mapping(bytes32 => PendingState) m_pending;
  bytes32[] m_pendingIndex;

}
