from mythril.laser.plugin import LaserPlugin
from mythril.laser.plugin.plugins.mutation_pruner import MutationPruner
from mythril.laser.plugin.plugins.dependency_pruner import DependencyPruner
from mythril.laser.plugin.plugins.coverage import InstructionCoveragePlugin


class PluginFactory:
    """ The plugin factory constructs the plugins provided with laser """

    @staticmethod
    def build_benchmark_plugin(name: str) -> LaserPlugin:
        """ Creates an instance of the benchmark plugin with the given name """
        from mythril.laser.plugin.plugins.benchmark import BenchmarkPlugin

        return BenchmarkPlugin(name)

    @staticmethod
    def build_mutation_pruner_plugin() -> LaserPlugin:
        """ Creates an instance of the mutation pruner plugin"""
        from mythril.laser.plugin import MutationPruner

        return MutationPruner()

    @staticmethod
    def build_instruction_coverage_plugin() -> LaserPlugin:
        """ Creates an instance of the instruction coverage plugin"""
        from mythril.laser.plugin import InstructionCoveragePlugin

        return InstructionCoveragePlugin()

    @staticmethod
    def build_dependency_pruner_plugin() -> LaserPlugin:
        """ Creates an instance of the mutation pruner plugin"""
        from mythril.laser.plugin import DependencyPruner

        return DependencyPruner()
