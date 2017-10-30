from mythril.ether.ethcontract import ETHContract

class DynLoader:

	def __init__(self, eth):
		self.eth = eth

	def dynld(self, address):

		contract = ETHContract(self.eth.eth_getCode(address), name=address, address=address)
		return contract.as_dict()