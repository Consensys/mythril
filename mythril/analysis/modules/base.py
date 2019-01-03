import logging
from typing import List

log = logging.getLogger(__name__)


class DetectionModule:
    def __init__(
        self,
        name: str,
        swc_id: str,
        description: str,
        entrypoint: str = "post",
        pre_hooks: List[str] = None,
        post_hooks: List[str] = None,
    ):
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
        self.cache_addresses = {}

    def execute(self, statespace):
        raise NotImplementedError()

    def __repr__(self):
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
