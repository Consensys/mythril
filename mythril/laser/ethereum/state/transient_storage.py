"""This module contains account-related functionality.

This includes classes representing accounts and their storage.
"""
import logging
from copy import copy, deepcopy
from typing import Any, Dict, Union, Set


from mythril.laser.smt import Array, K, BitVec, simplify, BaseArray, If, Bool
from mythril.disassembler.disassembly import Disassembly
from mythril.laser.smt import symbol_factory
from mythril.support.support_args import args

log = logging.getLogger(__name__)


from pysmt.shortcuts import (
    Symbol,
    Array,
    Store,
    Select,
    ArrayType,
    Solver,
    BV,
    Equals,
    BVZero,
    BVConcat,
)


class TransientStorage:
    def __init__(self):
        self.checkpoints = [
            0
        ]  # List to store lengths of the journal at each checkpoint

        # Define symbolic arrays for current state and journal
        self.current_array = Array("current", ArrayType(BV(256), BV(256)))
        self.journal_array = Array(
            "journal", ArrayType(BV(256), ArrayType(BV(256), BV(256)))
        )

        # Function to get value from current state
        self.get_func = Select(self.current_array, addr)[key]

        # Function to update current state
        self.update_current_func = Store(
            self.current_array,
            addr,
            Store(Select(self.current_array, addr), key, prevValue),
        )

    def get(self, addr, key):
        # Create symbolic variables for address and key
        addr_sym = BVConcat(BVZero(96), addr)
        key_sym = BVConcat(BVZero(96), key)

        # Call SMT solver to get value from current state
        solver = Solver()
        solver.add(
            Equals(self.get_func.simplify({addr: addr_sym, key: key_sym}), BVZero(256))
        )
        if solver.solve():
            model = solver.get_model()
            return model.get_value(self.get_func)
        else:
            return BVZero(256)  # Return symbolic zero if value is not found

    def put(self, addr, key, value):
        # Create symbolic variables for address, key, and value
        addr_sym = BVConcat(BVZero(96), addr)
        key_sym = BVConcat(BVZero(96), key)
        value_sym = BVConcat(BVZero(96), value)

        # Store the journal entry
        self.journal.append((addr_sym, key_sym, self.get(addr, key)))

        # Update the current state
        self.current_array = self.update_current_func.simplify(
            {addr: addr_sym, key: key_sym, prevValue: value_sym}
        )

    def commit(self):
        if len(self.checkpoints) == 0:
            raise ValueError("Nothing to commit")
        self.checkpoints.pop()  # The last checkpoint is discarded.

    def checkpoint(self):
        self.checkpoints.append(len(self.journal))

    def revert(self):
        last_checkpoint = self.checkpoints.pop()
        if last_checkpoint is None:
            raise ValueError("Nothing to revert")

        for i in range(len(self.journal) - 1, last_checkpoint - 1, -1):
            (addr, key, prevValue) = self.journal[i]
            self.current_array = Store(
                self.current_array,
                addr,
                Store(Select(self.current_array, addr), key, prevValue),
            )
        self.journal = self.journal[:last_checkpoint]
