from collections import defaultdict
from typing import List, Optional, Callable, Mapping, Dict
import logging

from mythril.support.opcodes import OPCODES
from mythril.analysis.module.base import DetectionModule, EntryPoint
from mythril.analysis.module.loader import ModuleLoader

log = logging.getLogger(__name__)
OP_CODE_LIST = OPCODES.keys()


def get_detection_module_hooks(
    modules: List[DetectionModule], hook_type="pre"
) -> Dict[str, List[Callable]]:
    """Gets a dictionary with the hooks for the passed detection modules

    :param modules: The modules for which to retrieve hooks
    :param hook_type: The type  of hooks to retrieve (default: "pre")
    :return: Dictionary with discovered hooks
    """
    hook_dict = defaultdict(list)  # type: Mapping[str, List[Callable]]
    for module in modules:

        hooks = module.pre_hooks if hook_type == "pre" else module.post_hooks

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


def reset_callback_modules(module_names: Optional[List[str]] = None):
    """Clean the issue records of every callback-based module."""
    modules = ModuleLoader().get_detection_modules(EntryPoint.CALLBACK, module_names)
    for module in modules:
        module.reset_module()
