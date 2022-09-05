#!/usr/bin/env python3
# -*- coding: utf-8 -*-

import logging
import traceback
from typing import Optional, List
from argparse import Namespace

from . import MythrilDisassembler
from mythril.support.source_support import Source
from mythril.support.loader import DynLoader
from mythril.support.support_args import args
from mythril.analysis.symbolic import SymExecWrapper
from mythril.analysis.callgraph import generate_graph
from mythril.analysis.traceexplore import get_serializable_statespace
from mythril.analysis.security import fire_lasers, retrieve_callback_issues
from mythril.analysis.report import Report, Issue
from mythril.ethereum.evmcontract import EVMContract
from mythril.laser.smt import SolverStatistics
from mythril.support.start_time import StartTime
from mythril.exceptions import DetectorNotFoundError
from mythril.laser.execution_info import ExecutionInfo

log = logging.getLogger(__name__)


class MythrilAnalyzer:
    """
    The Mythril Analyzer class
    Responsible for the analysis of the smart contracts
    """

    def __init__(
        self,
        disassembler: MythrilDisassembler,
        cmd_args: Namespace,
        strategy: str = "dfs",
        address: Optional[str] = None,
    ):
        """

        :param disassembler: The MythrilDisassembler class
        :param cmd_args: The command line args Namespace
        :param strategy: Search strategy
        :param address: Address of the contract
        """
        self.eth = disassembler.eth
        self.contracts = disassembler.contracts or []  # type: List[EVMContract]
        self.enable_online_lookup = disassembler.enable_online_lookup
        self.use_onchain_data = not cmd_args.no_onchain_data
        self.strategy = strategy
        self.address = address
        self.max_depth = cmd_args.max_depth
        self.execution_timeout = cmd_args.execution_timeout
        self.loop_bound = cmd_args.loop_bound
        self.create_timeout = cmd_args.create_timeout
        self.disable_dependency_pruning = cmd_args.disable_dependency_pruning
        self.custom_modules_directory = (
            cmd_args.custom_modules_directory
            if cmd_args.custom_modules_directory
            else ""
        )
        args.pruning_factor = cmd_args.pruning_factor
        args.solver_timeout = cmd_args.solver_timeout
        args.parallel_solving = cmd_args.parallel_solving
        args.unconstrained_storage = cmd_args.unconstrained_storage
        args.call_depth_limit = cmd_args.call_depth_limit
        args.iprof = cmd_args.enable_iprof
        args.solver_log = cmd_args.solver_log
        args.transaction_sequences = cmd_args.transaction_sequences

    def dump_statespace(self, contract: EVMContract = None) -> str:
        """
        Returns serializable statespace of the contract
        :param contract: The Contract on which the analysis should be done
        :return: The serialized state space
        """
        sym = SymExecWrapper(
            contract or self.contracts[0],
            self.address,
            self.strategy,
            dynloader=DynLoader(self.eth, active=self.use_onchain_data),
            max_depth=self.max_depth,
            execution_timeout=self.execution_timeout,
            create_timeout=self.create_timeout,
            disable_dependency_pruning=self.disable_dependency_pruning,
            run_analysis_modules=False,
            custom_modules_directory=self.custom_modules_directory,
        )

        return get_serializable_statespace(sym)

    def graph_html(
        self,
        contract: EVMContract = None,
        enable_physics: bool = False,
        phrackify: bool = False,
        transaction_count: Optional[int] = None,
    ) -> str:
        """

        :param contract: The Contract on which the analysis should be done
        :param enable_physics: If true then enables the graph physics simulation
        :param phrackify: If true generates Phrack-style call graph
        :param transaction_count: The amount of transactions to be executed
        :return: The generated graph in html format
        """

        sym = SymExecWrapper(
            contract or self.contracts[0],
            self.address,
            self.strategy,
            dynloader=DynLoader(self.eth, active=self.use_onchain_data),
            max_depth=self.max_depth,
            execution_timeout=self.execution_timeout,
            transaction_count=transaction_count,
            create_timeout=self.create_timeout,
            disable_dependency_pruning=self.disable_dependency_pruning,
            run_analysis_modules=False,
            custom_modules_directory=self.custom_modules_directory,
        )
        return generate_graph(sym, physics=enable_physics, phrackify=phrackify)

    def fire_lasers(
        self,
        modules: Optional[List[str]] = None,
        transaction_count: Optional[int] = None,
    ) -> Report:
        """
        :param modules: The analysis modules which should be executed
        :param transaction_count: The amount of transactions to be executed
        :return: The Report class which contains the all the issues/vulnerabilities
        """
        all_issues = []  # type: List[Issue]
        SolverStatistics().enabled = True
        exceptions = []
        execution_info = None  # type: Optional[List[ExecutionInfo]]
        for contract in self.contracts:
            StartTime()  # Reinitialize start time for new contracts
            try:
                sym = SymExecWrapper(
                    contract,
                    self.address,
                    self.strategy,
                    dynloader=DynLoader(self.eth, active=self.use_onchain_data),
                    max_depth=self.max_depth,
                    execution_timeout=self.execution_timeout,
                    loop_bound=self.loop_bound,
                    create_timeout=self.create_timeout,
                    transaction_count=transaction_count,
                    modules=modules,
                    compulsory_statespace=False,
                    disable_dependency_pruning=self.disable_dependency_pruning,
                    custom_modules_directory=self.custom_modules_directory,
                )
                issues = fire_lasers(sym, modules)
                execution_info = sym.execution_info
            except DetectorNotFoundError as e:
                # Bubble up
                raise e
            except KeyboardInterrupt:
                log.critical("Keyboard Interrupt")
                issues = retrieve_callback_issues(modules)
            except Exception:
                log.critical(
                    "Exception occurred, aborting analysis. Please report this issue to the Mythril GitHub page.\n"
                    + traceback.format_exc()
                )
                issues = retrieve_callback_issues(modules)
                exceptions.append(traceback.format_exc())
            for issue in issues:
                issue.add_code_info(contract)

            all_issues += issues
            log.info("Solver statistics: \n{}".format(str(SolverStatistics())))

        source_data = Source()
        source_data.get_source_from_contracts_list(self.contracts)

        # Finally, output the results
        report = Report(
            contracts=self.contracts,
            exceptions=exceptions,
            execution_info=execution_info,
        )
        for issue in all_issues:
            report.append_issue(issue)

        return report
