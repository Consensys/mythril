import logging
from mythril import ether
import time
from ethereum.messages import Log
import rlp
from rlp.sedes import big_endian_int, binary
from ethereum import utils
from ethereum.utils import hash32, address, int256
from mythril.exceptions import AddressNotFoundError

BATCH_SIZE = 8 * 4096


class CountableList(object):
    """A sedes for lists of arbitrary length.
    :param element_sedes: when (de-)serializing a list, this sedes will be
                          applied to all of its elements
    """

    def __init__(self, element_sedes):
        self.element_sedes = element_sedes

    def serialize(self, obj):
        return [self.element_sedes.serialize(e) for e in obj]

    def deserialize(self, serial):
        # needed for 2 reasons:
        # 1. empty lists are not zero elements
        # 2. underlying logs are stored as list - if empty will also except and receipts will be lost
        try:
            return [self.element_sedes.deserialize(e) for e in serial]
        except:
            return []


class ReceiptForStorage(rlp.Serializable):
    '''
    Receipt format stored in levelDB
    '''

    fields = [
        ('state_root', binary),
        ('cumulative_gas_used', big_endian_int),
        ('bloom', int256),
        ('tx_hash', hash32),
        ('contractAddress', address),
        ('logs', CountableList(Log)),
        ('gas_used', big_endian_int)
    ]


class AccountIndexer(object):
    '''
    Updates address index
    '''

    def __init__(self, ethDB):
        self.db = ethDB
        self.lastBlock = None
        self.lastProcessedBlock = None

        self.updateIfNeeded()

    def get_contract_by_hash(self, contract_hash):
        '''
        get mapped contract_address by its hash, if not found try indexing
        '''
        contract_address = self.db.reader._get_address_by_hash(contract_hash)
        if contract_address is not None:
            return contract_address
        else:
            raise AddressNotFoundError

    def _process(self, startblock):
        '''
        Processesing method
        '''
        logging.debug("Processing blocks %d to %d" % (startblock, startblock + BATCH_SIZE))

        addresses = []

        for blockNum in range(startblock, startblock + BATCH_SIZE):
            block_hash = self.db.reader._get_block_hash(blockNum)
            if block_hash is not None:
                receipts = self.db.reader._get_block_receipts(block_hash, blockNum)

                for receipt in receipts:
                    if receipt.contractAddress is not None and not all(b == 0 for b in receipt.contractAddress):
                        addresses.append(receipt.contractAddress)
            else:
                if len(addresses) == 0:
                    raise Exception()

        return addresses

    def updateIfNeeded(self):
        '''
        update address index
        '''
        headBlock = self.db.reader._get_head_block()
        if headBlock is not None:
            # avoid restarting search if head block is same & we already initialized
            # this is required for fastSync handling
            if self.lastBlock is not None:
                self.lastBlock = max(self.lastBlock, headBlock.number)
            else:
                self.lastBlock = headBlock.number
        lastProcessed = self.db.reader._get_last_indexed_number()
        if lastProcessed is not None:
            self.lastProcessedBlock = utils.big_endian_to_int(lastProcessed)

        # in fast sync head block is at 0 (e.g. in fastSync), we can't use it to determine length
        if self.lastBlock is not None and self.lastBlock == 0:
            self.lastBlock = 2e+9

        if self.lastBlock is None or (self.lastProcessedBlock is not None and self.lastBlock <= self.lastProcessedBlock):
            return

        blockNum = 0
        if self.lastProcessedBlock is not None:
            blockNum = self.lastProcessedBlock + 1
            print("Updating hash-to-address index from block " + str(self.lastProcessedBlock))
        else:
            print("Starting hash-to-address index")

        count = 0
        processed = 0

        while (blockNum <= self.lastBlock):
            # leveldb cannot be accessed on multiple processes (not even readonly)
            # multithread version performs significantly worse than serial
            try:
                results = self._process(blockNum)
            except:
                break

            # store new mappings
            self.db.writer._start_writing()
            count += len(results)
            for addr in results:
                self.db.writer._store_account_address(addr)

            self.db.writer._commit_batch()

            processed += BATCH_SIZE
            blockNum = min(blockNum + BATCH_SIZE, self.lastBlock + 1)

            cost_time = time.time() - ether.start_time
            print("%d blocks processed (in %d seconds), %d unique addresses found, next block: %d" % (processed, cost_time, count, min(self.lastBlock, blockNum)))

            self.lastProcessedBlock = blockNum - 1
            self.db.writer._set_last_indexed_number(self.lastProcessedBlock)

        print("Finished indexing")
        self.lastBlock = self.lastProcessedBlock
