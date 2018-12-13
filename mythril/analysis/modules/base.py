import logging
from typing import List


class DetectionModule:
    """The base detection module.
    
    All custom-built detection modules must inherit from this class.
    """
    def __init__(
        self,
        name: str,
        swc_id: str,
        hooks: List[str],
        description: str,
        entrypoint: str = "post",
    ) -> None:
        """

        :param name: 
        :param swc_id: 
        :param hooks: 
        :param description: 
        :param entrypoint: 
        """
        self.name = name
        self.swc_id = swc_id
        self.hooks = hooks
        self.description = description
        if entrypoint not in ("post", "callback"):
            logging.error(
                "Invalid entrypoint in module %s, must be one of {post, callback}",
                self.name,
            )
        self.entrypoint = entrypoint

    def execute(self, statespace):
        """ The entry point for execution, which is being called by Mythril.
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
            "hooks={0.hooks} "
            "description={0.description}"
            ">"
        ).format(self)
