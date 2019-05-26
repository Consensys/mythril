"""This module contains the base class for all user-defined detection
modules."""

import logging
from typing import List
from mythril.analysis.report import Issue

log = logging.getLogger(__name__)


class DetectionModule:
    """The base detection module.

    All custom-built detection modules must inherit from this class.
    """

    def __init__(
        self,
        name: str,
        swc_id: str,
        description: str,
        entrypoint: str = "post",
        pre_hooks: List[str] = None,
        post_hooks: List[str] = None,
    ) -> None:
        self.name = name
        self.swc_id = swc_id
        self.pre_hooks = pre_hooks if pre_hooks else []
        self.post_hooks = post_hooks if post_hooks else []
        self.description = description
        if entrypoint not in ("post", "callback"):
            log.error(
                "Invalid entrypoint in module %s, must be one of {post, callback}",
                self.name,
            )
        self.entrypoint = entrypoint
        self._issues = []  # type: List[Issue]

    @property
    def issues(self):
        """
        Returns the issues
        """
        return self._issues

    def reset_module(self):
        """
        Resets issues
        """
        self._issues = []

    def execute(self, statespace):
        """The entry point for execution, which is being called by Mythril.

        :param statespace:
        :return:
        """

        log.debug("Entering analysis module: {}".format(self.__class__.__name__))

        self._execute(statespace)

        log.debug("Exiting analysis module: {}".format(self.__class__.__name__))

    def _execute(self, statespace):
        """Module main method (override this)

        :param statespace:
        :return:
        """

        raise NotImplementedError()

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
