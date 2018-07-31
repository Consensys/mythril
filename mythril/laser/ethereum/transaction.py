import logging
from mythril.disassembler.disassembly import Disassembly
from mythril.laser.ethereum.state import GlobalState, Environment, CalldataType
from mythril.laser.ethereum.cfg import Node, Edge, JumpType
from z3 import BitVec


class TransactionEndSignal(IndexError):
    def __init__(self, global_state):
        self.global_state = global_state


class TransactionStartSignal(Exception):

    def __init__(self, transaction, op_code):
        self.transaction = transaction
        self.op_code = op_code


class CallTransaction:
    def __init__(self,
                 world_state,
                 callee_account,
                 caller,
                 call_data=(),
                 gas_price=BitVec("gasprice", 256),
                 call_value=BitVec("callvalue", 256),
                 origin=BitVec("origin", 256),
                 call_data_type=BitVec("call_data_type", 256)
                 ):
        self.world_state = world_state
        self.callee_account = callee_account
        self.caller = caller
        self.call_data = call_data
        self.gas_price = gas_price
        self.call_value = call_value
        self.origin = origin
        self.call_data_type = call_data_type

        self.return_data = None

    def initial_global_state(self):
        # Initialize the execution environment
        environment = Environment(
            self.callee_account,
            self.caller,
            self.call_data,
            self.gas_price,
            self.call_value,
            self.origin,
            code=self.callee_account.code,
            calldata_type=self.call_data_type,
        )

        global_state = GlobalState(self.world_state.accounts, environment, None)
        global_state.environment.active_function_name = 'fallback'

        return global_state

    def end(self, global_state, return_data=None):
        self.return_data = return_data
        raise TransactionEndSignal(global_state)


class Transaction:
    def __init__(self):
        self.open_states = None

    @property
    def has_ran(self):
        return self.open_states is not None

    def run(self, open_world_states, evm):
        raise NotImplementedError()


class MessageCall(Transaction):

    """ Represents a call value transaction """
    def __init__(self, callee_address):
        """
        Constructor for Call transaction, sets up all symbolic parameters
        :param callee_address: Address of the contract that will be called
        """
        self.callee_address = callee_address
        self.caller = BitVec("caller", 256)
        self.gas_price = BitVec("gasprice", 256)
        self.call_value = BitVec("callvalue", 256)
        self.origin = BitVec("origin", 256)
        Transaction.__init__(self)

    def run(self, open_world_states: list, evm):
        """ Runs this transaction on the evm starting from the open world states """
        # Consume the open states
        open_states = open_world_states[:]
        del open_world_states[:]

        for open_world_state in open_states:

            transaction = CallTransaction(
                open_world_state,
                open_world_state[self.callee_address],
                self.caller,
                [],
                self.gas_price,
                self.call_value,
                self.origin,
                CalldataType.SYMBOLIC,
            )
            global_state = transaction.initial_global_state()
            global_state.transaction_stack.append((transaction, None))

            new_node = Node(global_state.environment.active_account.contract_name)
            evm.instructions_covered = [False for _ in global_state.environment.code.instruction_list]

            evm.nodes[new_node.uid] = new_node
            if open_world_state.node:
                evm.edges.append(Edge(open_world_state.node.uid, new_node.uid, edge_type=JumpType.Transaction, condition=None))
            global_state.node = new_node
            new_node.states.append(global_state)
            evm.work_list.append(global_state)

        evm.exec()
        logging.info("Execution complete")
        logging.info("Achieved {0:.3g}% coverage".format(evm.coverage))


class ContractCreation(Transaction):
    """ Represents a contract creation transaction"""

    def __init__(self, creation_code):
        """
        Constructor for ContractCreation, sets up all symbolic parameters
        :param creation_code: Contract creation code for this contract
        """
        self.caller = BitVec("caller", 256)
        self.gas_price = BitVec("gasprice", 256)
        self.origin = BitVec("origin", 256)

        self.init = creation_code

        Transaction.__init__(self)

    def run(self, open_world_states: list, evm):
        """ Runs this transaction on the evm starting from the open world states """
        # Consume the open states
        open_states = open_world_states[:]
        del open_world_states[:]

        for open_world_state in open_states:
            new_account = open_world_state.create_account()

            # Initialize the execution environment
            environment = Environment(
                new_account,
                self.caller,
                [],
                self.gas_price,
                None,
                self.origin,
                code=Disassembly(self.init),
                calldata_type=CalldataType.SYMBOLIC,
            )

            new_node = Node(environment.active_account.contract_name)
            evm.instructions_covered = [False for _ in environment.code.instruction_list]

            evm.nodes[new_node.uid] = new_node
            if open_world_state.node:
                evm.edges.append(Edge(open_world_state.node.uid, new_node.uid, edge_type=JumpType.Transaction, condition=None))

            global_state = GlobalState(open_world_state, environment, new_node)
            new_node.states.append(global_state)

            evm.work_list.append(global_state)

        evm.exec()
        logging.info("Execution complete")
        logging.info("Achieved {0:.3g}% coverage".format(evm.coverage))
