from collections import namedtuple
from datetime import datetime
from typing import Dict, List, Tuple
from mythril.laser.plugin.builder import PluginBuilder
from mythril.laser.plugin.interface import LaserPlugin
from mythril.laser.ethereum.svm import LaserEVM
from mythril.laser.ethereum.state.global_state import GlobalState
from datetime import datetime
import logging

# Type annotations:
#   start_time: datetime
#   end_time: datetime
_InstrExecRecord = namedtuple("_InstrExecRecord", ["start_time", "end_time"])

# Type annotations:
#   total_time: float
#   total_nr: float
#   min_time: float
#   max_time: float
_InstrExecStatistic = namedtuple(
    "_InstrExecStatistic", ["total_time", "total_nr", "min_time", "max_time"]
)

# Map the instruction opcode to its records if all execution times
_InstrExecRecords = Dict[str, List[_InstrExecRecord]]

# Map the instruction opcode to the statistic of its execution times
_InstrExecStatistics = Dict[str, _InstrExecStatistic]

log = logging.getLogger(__name__)


class InstructionProfilerBuilder(PluginBuilder):
    name = "instruction-profiler"

    def __call__(self, *args, **kwargs):
        return InstructionProfiler()


class InstructionProfiler(LaserPlugin):
    """Performance profile for the execution of each instruction."""

    def __init__(self):
        self._reset()

    def _reset(self):
        self.records = dict()
        self.start_time = None

    def initialize(self, symbolic_vm: LaserEVM) -> None:
        @symbolic_vm.instr_hook("pre", None)
        def get_start_time(op_code: str):
            def start_time_wrapper(global_state: GlobalState):
                self.start_time = datetime.now()

            return start_time_wrapper

        @symbolic_vm.instr_hook("post", None)
        def record(op_code: str):
            def record_opcode(global_state: GlobalState):
                end_time = datetime.now()
                try:
                    self.records[op_code].append(
                        _InstrExecRecord(self.start_time, end_time)
                    )
                except KeyError:
                    self.records[op_code] = [
                        _InstrExecRecord(self.start_time, end_time)
                    ]

            return record_opcode

        @symbolic_vm.laser_hook("stop_sym_exec")
        def print_stats():
            total, stats = self._make_stats()

            s = "Total: {} s\n".format(total)

            for op in sorted(stats):
                stat = stats[op]
                s += "[{:12s}] {:>8.4f} %,  nr {:>6},  total {:>8.4f} s,  avg {:>8.4f} s,  min {:>8.4f} s,  max {:>8.4f} s\n".format(
                    op,
                    stat.total_time * 100 / total,
                    stat.total_nr,
                    stat.total_time,
                    stat.total_time / stat.total_nr,
                    stat.min_time,
                    stat.max_time,
                )

            log.info(s)

    def _make_stats(self) -> Tuple[float, _InstrExecStatistics]:
        periods = {
            op: list(
                map(lambda r: r.end_time.timestamp() - r.start_time.timestamp(), rs)
            )
            for op, rs in self.records.items()
        }

        stats = dict()
        total_time = 0

        for _, (op, times) in enumerate(periods.items()):
            stat = _InstrExecStatistic(
                total_time=sum(times),
                total_nr=len(times),
                min_time=min(times),
                max_time=max(times),
            )
            total_time += stat.total_time
            stats[op] = stat

        return total_time, stats
