from mythril.analysis.module.base import DetectionModule, EntryPoint
from mythril.support.support_utils import Singleton

from mythril.analysis.module.modules.arbitrary_jump import ArbitraryJump
from mythril.analysis.module.modules.arbitrary_write import ArbitraryStorage
from mythril.analysis.module.modules.delegatecall import ArbitraryDelegateCall
from mythril.analysis.module.modules.dependence_on_predictable_vars import (
    PredictableVariables,
)
from mythril.analysis.module.modules.dependence_on_origin import TxOrigin
from mythril.analysis.module.modules.ether_thief import EtherThief
from mythril.analysis.module.modules.exceptions import Exceptions
from mythril.analysis.module.modules.external_calls import ExternalCalls
from mythril.analysis.module.modules.integer import IntegerArithmetics
from mythril.analysis.module.modules.multiple_sends import MultipleSends
from mythril.analysis.module.modules.state_change_external_calls import (
    StateChangeAfterCall,
)
from mythril.analysis.module.modules.suicide import AccidentallyKillable
from mythril.analysis.module.modules.unchecked_retval import UncheckedRetval
from mythril.analysis.module.modules.user_assertions import UserAssertions

from mythril.analysis.module.base import EntryPoint

from mythril.exceptions import DetectorNotFoundError

from typing import Optional, List


class ModuleLoader(object, metaclass=Singleton):
    """ModuleLoader

    The module loader class implements a singleton loader for detection modules.

    By default it will load the detection modules in the mythril package.
    Additional detection modules can be loaded using the register_module function call implemented by the ModuleLoader
    """

    def __init__(self):
        self._modules = []
        self._register_mythril_modules()

    def register_module(self, detection_module: DetectionModule):
        """Registers a detection module with the module loader"""
        if not isinstance(detection_module, DetectionModule):
            raise ValueError("The passed variable is not a valid detection module")
        self._modules.append(detection_module)

    def get_detection_modules(
        self,
        entry_point: Optional[EntryPoint] = None,
        white_list: Optional[List[str]] = None,
    ) -> List[DetectionModule]:
        """Gets registered detection modules

        :param entry_point: If specified: only return detection modules with this entry point
        :param white_list: If specified: only return whitelisted detection modules
        :return: The selected detection modules
        """

        result = self._modules[:]

        if white_list:

            # Sanity check

            available_names = [type(module).__name__ for module in result]

            for name in white_list:
                if name not in available_names:
                    raise DetectorNotFoundError(
                        "Invalid detection module: {}".format(name)
                    )

            result = [
                module for module in result if type(module).__name__ in white_list
            ]

        if entry_point:
            result = [module for module in result if module.entry_point == entry_point]

        return result

    def _register_mythril_modules(self):
        self._modules.extend(
            [
                ArbitraryJump(),
                ArbitraryStorage(),
                ArbitraryDelegateCall(),
                PredictableVariables(),
                TxOrigin(),
                EtherThief(),
                Exceptions(),
                ExternalCalls(),
                IntegerArithmetics(),
                MultipleSends(),
                StateChangeAfterCall(),
                AccidentallyKillable(),
                UncheckedRetval(),
                UserAssertions(),
            ]
        )
