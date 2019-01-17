from collections import namedtuple
from datetime import datetime
from typing import Dict, List, Tuple

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


class InstructionProfiler:
    """Performance profile for the execution of each instruction.
    """

    def __init__(self):
        self.records = dict()

    def record(self, op: int, start_time: datetime, end_time: datetime):
        try:
            self.records[op].append(_InstrExecRecord(start_time, end_time))
        except KeyError:
            self.records[op] = [_InstrExecRecord(start_time, end_time)]

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

    def __str__(self):
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

        return s
