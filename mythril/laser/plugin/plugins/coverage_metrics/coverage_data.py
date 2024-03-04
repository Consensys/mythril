import json
from typing import Dict, List

from mythril.support.support_utils import get_code_hash
from mythril.laser.execution_info import ExecutionInfo


class InstructionCoverageInfo(ExecutionInfo):
    def __init__(self):
        self._instruction_coverage = {}  # type: Dict[str, int]

    def as_dict(self):
        return dict(instruction_discovery_time=self._instruction_coverage)

    def get_code_instr_hex(self, code: str, instruction: int):
        code_hash = get_code_hash(code)[2:]
        instruction_hex = hex(instruction)[2:]
        return "{}:{}".format(code_hash, instruction_hex)

    def is_covered(self, code: str, instruction: int):
        code_instr_hex = self.get_code_instr_hex(code, instruction)
        return code_instr_hex in self._instruction_coverage

    def add_data(self, code: str, instruction: int, discovery_time: int):
        code_instr_hex = self.get_code_instr_hex(code, instruction)
        self._instruction_coverage[code_instr_hex] = discovery_time

    def output(self, filename: str):
        with open(filename, "w") as outfile:
            json.dump(
                self._instruction_coverage, default=lambda o: o.__dict__, fp=outfile
            )


class CoverageData:
    def __init__(
        self,
        instructions_covered: int,
        total_instructions: int,
        branches_covered: int,
        tx_id: int,
        total_branches: int,
        state_counter: int,
        code: str,
        time_elapsed: int,
    ):
        self.instructions_covered = instructions_covered
        self.total_instructions = total_instructions
        self.branches_covered = branches_covered
        self.tx_id = tx_id
        self.total_branches = total_branches
        self.state_counter = state_counter
        self.code_hash = get_code_hash(code)[2:]
        self.time_elapsed = time_elapsed

    def as_dict(self):
        return self.__dict__


class CoverageTimeSeries(ExecutionInfo):
    def __init__(self):
        self.coverage = []  # type: List[CoverageData]

    def output(self, filename: str):
        with open(filename, "w") as outfile:
            json.dump(self.coverage, default=lambda o: o.__dict__, fp=outfile)

    def as_dict(self):
        return dict(coverage=self.coverage)

    def add_data(self, *args, **kwargs):
        cov_data = CoverageData(*args, **kwargs)
        self.coverage.append(cov_data.as_dict())
