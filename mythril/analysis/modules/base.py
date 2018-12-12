import logging
from typing import List

log = logging.getLogger(__name__)


class DetectionModule:
    def __init__(
        self,
        name: str,
        swc_id: str,
        hooks: List[str],
        description: str,
        entrypoint: str = "post",
    ):
        self.name = name
        self.swc_id = swc_id
        self.hooks = hooks
        self.description = description
        if entrypoint not in ("post", "callback"):
            log.error(
                "Invalid entrypoint in module %s, must be one of {post, callback}",
                self.name,
            )
        self.entrypoint = entrypoint

    def execute(self, statespace):
        raise NotImplementedError()

    def __repr__(self):
        return (
            "<"
            "DetectionModule "
            "name={0.name} "
            "swc_id={0.swc_id} "
            "hooks={0.hooks} "
            "description={0.description}"
            ">"
        ).format(self)
