from collections import defaultdict
from typing import List
import logging

from mythril.support.opcodes import opcodes
from mythril.analysis.module.base import DetectionModule

log = logging.getLogger(__name__)
OP_CODE_LIST = [c[0] for _, c in opcodes.items()]


def get_detection_module_hooks(modules: List[DetectionModule], hook_type="pre"):
    """ Gets a dictionary with the hooks for the passed detection modules

    :param modules: The modules for which to retrieve hooks
    :param hook_type: The type  of hooks to retrieve (default: "pre")
    :return: Dictionary with discovered hooks
    """
    hook_dict = defaultdict(list)
    for module in modules:

        hooks = (
            module.detector.pre_hooks
            if hook_type == "pre"
            else module.detector.post_hooks
        )

        for op_code in map(lambda x: x.upper(), hooks):
            # A hook can be either OP_CODE or START*
            # When an entry like the second is encountered we hook all opcodes that start with START
            if op_code in OP_CODE_LIST:
                hook_dict[op_code].append(module.execute)
            elif op_code.endswith("*"):
                to_register = filter(lambda x: x.startswith(op_code[:-1]), OP_CODE_LIST)
                for actual_hook in to_register:
                    hook_dict[actual_hook].append(module.execute)
            else:
                log.error(
                    "Encountered invalid hook opcode %s in module %s",
                    op_code,
                    module.name,
                )

    return dict(hook_dict)
