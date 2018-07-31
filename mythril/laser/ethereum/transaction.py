import logging
from mythril.laser.ethereum.state import GlobalState, Environment, CalldataType
from mythril.laser.ethereum.cfg import Node, Edge, JumpType
from z3 import BitVec


class MessageCall:

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

        self.open_states = None

    @property
    def has_ran(self):
        return self.open_states is not None

    def run(self, open_world_states: list, evm):
        """ Runs this transaction on the evm starting from the open world states """
        # Consume the open states
        open_states = open_world_states[:]
        del open_world_states[:]

        for open_world_state in open_states:

            # Initialize the execution environment
            environment = Environment(
                open_world_state[self.callee_address],
                self.caller,
                [],
                self.gas_price,
                self.call_value,
                self.origin,
                calldata_type=CalldataType.SYMBOLIC,
            )
            new_node = Node(environment.active_account.contract_name)
            evm.instructions_covered = [False for _ in environment.code.instruction_list]

            evm.nodes[new_node.uid] = new_node
            if open_world_state.node:
                evm.edges.append(Edge(open_world_state.node.uid, new_node.uid, edge_type=JumpType.Transaction, condition=None))

            global_state = GlobalState(open_world_state.accounts, environment, new_node)
            global_state.environment.active_function_name = 'unnamed fallback'
            new_node.states.append(global_state)

            evm.work_list.append(global_state)

        evm.exec()
        logging.info("Execution complete")
        logging.info("Achieved {0:.3g}% coverage".format(evm.coverage))
