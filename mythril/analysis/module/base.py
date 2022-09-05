""" Mythril Detection Modules

This module includes an definition of the DetectionModule interface.
DetectionModules implement different analysis rules to find weaknesses and vulnerabilities.
"""
import logging
from typing import List, Set, Optional, Tuple

from mythril.analysis.report import Issue
from mythril.laser.ethereum.state.global_state import GlobalState
from mythril.support.support_args import args
from mythril.support.support_utils import get_code_hash
from abc import ABC, abstractmethod
from enum import Enum

# Get logger instance
log = logging.getLogger(__name__)


class EntryPoint(Enum):
    """EntryPoint Enum

    This enum is used to signify the entry_point of detection modules.
    See also the class documentation of DetectionModule
    """

    POST = 1
    CALLBACK = 2


class DetectionModule(ABC):
    """The base detection module.

    All custom-built detection modules must inherit from this class.

    There are several class properties that expose information about the detection modules

    :param name: The name of the detection module
    :param swc_id: The SWC ID associated with the weakness that the module detects
    :param description: A description of the detection module, and what it detects
    :param entry_point: Mythril can run callback style detection modules, or modules that search the statespace.
                [IMPORTANT] POST entry points severely slow down the analysis, try to always use callback style modules
    :param pre_hooks: A list of instructions to hook the laser vm for (pre execution of the instruction)
    :param post_hooks: A list of instructions to hook the laser vm for (post execution of the instruction)
    """

    name = "Detection Module Name / Title"
    swc_id = "SWC-000"
    description = "Detection module description"
    entry_point: EntryPoint = EntryPoint.CALLBACK
    pre_hooks: List[str] = []
    post_hooks: List[str] = []

    def __init__(self) -> None:
        self.issues: List[Issue] = []
        self.cache: Set[Tuple[int, str]] = set()
        self.auto_cache = True

    def reset_module(self):
        """Resets the storage of this module"""
        self.issues = []

    def update_cache(self, issues=None):
        """
        Updates cache with param issues, updates against self.issues, if the param is None
        :param issues: The issues used to update the cache
        """
        issues = issues or self.issues
        for issue in issues:
            self.cache.add((issue.address, issue.bytecode_hash))

    def execute(self, target: GlobalState) -> Optional[List[Issue]]:
        """The entry point for execution, which is being called by Mythril.

        :param target: The target of the analysis, either a global state (callback) or the entire statespace (post)
        :return: List of encountered issues
        """

        log.debug("Entering analysis module: {}".format(self.__class__.__name__))

        if (
            target.get_current_instruction()["address"],
            get_code_hash(target.environment.code.bytecode),
        ) in self.cache and self.auto_cache:
            log.debug(
                f"Issue in cache for the analysis module: {self.__class__.__name__}, address: {target.get_current_instruction()['address']}"
            )
            return []

        result = self._execute(target)
        log.debug("Exiting analysis module: {}".format(self.__class__.__name__))

        if result and not args.use_issue_annotations:
            if self.auto_cache:
                self.update_cache(result)
            self.issues += result

        return result

    @abstractmethod
    def _execute(self, target) -> Optional[List[Issue]]:
        """Module main method (override this)

        :param target: The target of the analysis, either a global state (callback) or the entire statespace (post)
        :return: List of encountered issues
        """
        pass

    def __repr__(self) -> str:
        return (
            "<"
            "DetectionModule "
            "name={0.name} "
            "swc_id={0.swc_id} "
            "pre_hooks={0.pre_hooks} "
            "post_hooks={0.post_hooks} "
            "description={0.description}"
            ">"
        ).format(self)
