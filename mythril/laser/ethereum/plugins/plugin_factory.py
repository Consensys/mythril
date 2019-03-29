from mythril.laser.ethereum.plugins.plugin import LaserPlugin
from mythril.laser.ethereum.plugins.implementations.benchmark import BenchmarkPlugin
from mythril.laser.ethereum.plugins.implementations.mutation_pruner import (
    MutationPruner,
)
from mythril.laser.ethereum.plugins.implementations.coverage import (
    InstructionCoveragePlugin,
)


class PluginFactory:
    """ The plugin factory constructs the plugins provided with laser """

    @staticmethod
    def build_benchmark_plugin(name: str) -> LaserPlugin:
        """ Creates an instance of the benchmark plugin with the given name """
        return BenchmarkPlugin(name)

    @staticmethod
    def build_mutation_pruner_plugin() -> LaserPlugin:
        """ Creates an instance of the mutation pruner plugin"""
        return MutationPruner()

    @staticmethod
    def build_instruction_coverage_plugin() -> LaserPlugin:
        """ Creates an instance of the instruction coverage plugin"""
        return InstructionCoveragePlugin()
