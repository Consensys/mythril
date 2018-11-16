from typing import List


class DetectionModule:
    def __init__(self, name: str, swc_id: str, hooks: List[str], description: str):
        self.name = name
        self.swc_id = swc_id
        self.hooks = hooks
        self.description = description

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
