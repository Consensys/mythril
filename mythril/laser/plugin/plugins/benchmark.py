from mythril.laser.ethereum.svm import LaserEVM
from mythril.laser.plugin.interface import LaserPlugin
from mythril.laser.plugin.builder import PluginBuilder
from time import time
import matplotlib.pyplot as plt
import logging

log = logging.getLogger(__name__)


class BenchmarkPluginBuilder(PluginBuilder):
    name = "benchmark"

    def __call__(self, *args, **kwargs):
        return BenchmarkPlugin()


# TODO: introduce dependency on coverage plugin
class BenchmarkPlugin(LaserPlugin):
    """Benchmark Plugin

    This plugin aggregates the following information:
    - duration
    - code coverage over time
    - final code coverage
    - total number of executed instructions

    """

    def __init__(self, name=None):
        """Creates BenchmarkPlugin

        :param name: name of this benchmark, used for storing the results
        """
        self.nr_of_executed_insns = 0
        self.begin = None
        self.end = None
        self.coverage = {}
        self.name = name

    def initialize(self, symbolic_vm: LaserEVM):
        """Initializes the BenchmarkPlugin

        Introduces hooks in symbolic_vm to track the desired values
        :param symbolic_vm: Symbolic virtual machine to analyze
        """
        self._reset()

        @symbolic_vm.laser_hook("execute_state")
        def execute_state_hook(_):
            current_time = time() - self.begin
            self.nr_of_executed_insns += 1

            for key, value in symbolic_vm.coverage.items():
                try:
                    self.coverage[key][current_time] = sum(value[1]) * 100 / value[0]
                except KeyError:
                    self.coverage[key] = {}
                    self.coverage[key][current_time] = sum(value[1]) * 100 / value[0]

        @symbolic_vm.laser_hook("start_sym_exec")
        def start_sym_exec_hook():
            self.begin = time()

        @symbolic_vm.laser_hook("stop_sym_exec")
        def stop_sym_exec_hook():
            self.end = time()

            self._write_to_graph()
            self._store_report()

    def _reset(self):
        """Reset this plugin"""
        self.nr_of_executed_insns = 0
        self.begin = None
        self.end = None
        self.coverage = {}

    def _store_report(self):
        """Store the results of this plugin"""
        pass

    def _write_to_graph(self):
        """Write the coverage results to a graph"""
        traces = []
        for _, trace_data in self.coverage.items():
            traces += [list(trace_data.keys()), list(trace_data.values()), "r--"]

        plt.plot(*traces)
        plt.axis([0, self.end - self.begin, 0, 100])
        plt.xlabel("Duration (seconds)")
        plt.ylabel("Coverage (percentage)")

        plt.savefig("{}.png".format(self.name))
