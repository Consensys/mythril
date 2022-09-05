"""This module contains functionality for hooking in detection modules and
executing them."""

from mythril.analysis.module import ModuleLoader, reset_callback_modules
from mythril.analysis.module.base import EntryPoint
from mythril.analysis.report import Issue

from typing import Optional, List
import logging

log = logging.getLogger(__name__)


def retrieve_callback_issues(white_list: Optional[List[str]] = None) -> List[Issue]:
    """Get the issues discovered by callback type detection modules"""
    issues = []  # type: List[Issue]
    for module in ModuleLoader().get_detection_modules(
        entry_point=EntryPoint.CALLBACK, white_list=white_list
    ):
        log.debug("Retrieving results for " + module.name)
        issues += module.issues

    reset_callback_modules(module_names=white_list)

    return issues


def fire_lasers(statespace, white_list: Optional[List[str]] = None) -> List[Issue]:
    """Fire lasers at analysed statespace object

    :param statespace: Symbolic statespace to analyze
    :param white_list: Optionally whitelist modules to use for the analysis
    :return: Discovered issues
    """
    log.info("Starting analysis")

    issues = []  # type: List[Issue]
    for module in ModuleLoader().get_detection_modules(
        entry_point=EntryPoint.POST, white_list=white_list
    ):
        log.info("Executing " + module.name)
        issues += module.execute(statespace)

    issues += retrieve_callback_issues(white_list)
    return issues
