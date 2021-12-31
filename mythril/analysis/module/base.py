""" Mythril Detection Modules

This module includes an definition of the DetectionModule interface.
DetectionModules implement different analysis rules to find weaknesses and vulnerabilities.
"""
import logging
from typing import List, Set, Optional, Tuple, Union

from mythril.analysis.report import Issue
from mythril.laser.ethereum.state.global_state import GlobalState

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
    - name: The name of the detection module
    - swc_id: The SWC ID associated with the weakness that the module detects
    - description: A description of the detection module, and what it detects
    - entry_point: Mythril can run callback style detection modules, or modules that search the statespace.
                [IMPORTANT] POST entry points severely slow down the analysis, try to always use callback style modules
    - pre_hooks: A list of instructions to hook the laser vm for (pre execution of the instruction)
    - post_hooks: A list of instructions to hook the laser vm for (post execution of the instruction)
    """

    name = "Detection Module Name / Title"
    swc_id = "SWC-000"
    description = "Detection module description"
    entry_point = EntryPoint.CALLBACK  # type: EntryPoint
    pre_hooks = []  # type: List[str]
    post_hooks = []  # type: List[str]

    def __init__(self) -> None:
        self.issues = []  # type: List[Issue]
        self.cache = set()  # type: Set[Optional[Union[int, Tuple[int, str]]]]

    def reset_module(self):
        """Resets the storage of this module"""
        self.issues = []

    def execute(self, target: GlobalState) -> Optional[List[Issue]]:
        """The entry point for execution, which is being called by Mythril.

        :param target: The target of the analysis, either a global state (callback) or the entire statespace (post)
        :return: List of encountered issues
        """

        log.debug("Entering analysis module: {}".format(self.__class__.__name__))

        result = self._execute(target)

        log.debug("Exiting analysis module: {}".format(self.__class__.__name__))

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
