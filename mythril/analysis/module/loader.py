from mythril.analysis.module.base import DetectionModule, EntryPoint
from mythril.support.support_utils import Singleton

from mythril.analysis.module.modules.arbitrary_jump import ArbitraryJump
from mythril.analysis.module.modules.arbitrary_write import ArbitraryStorage
from mythril.analysis.module.modules.delegatecall import DelegateCallModule
from mythril.analysis.module.modules.dependence_on_predictable_vars import PredictableDependenceModule
from mythril.analysis.module.modules.deprecated_ops import DeprecatedOperationsModule
from mythril.analysis.module.modules.ether_thief import EtherThief
from mythril.analysis.module.modules.exceptions import ReachableExceptionsModule
from mythril.analysis.module.modules.external_calls import ExternalCalls
from mythril.analysis.module.modules.integer import IntegerOverflowUnderflowModule
from mythril.analysis.module.modules.multiple_sends import MultipleSendsModule
from mythril.analysis.module.modules.state_change_external_calls import StateChange
from mythril.analysis.module.modules.suicide import SuicideModule
from mythril.analysis.module.modules.unchecked_retval import UncheckedRetvalModule
from mythril.analysis.module.modules.user_assertions import UserAssertions


class ModuleLoader(object, metaclass=Singleton):
    def __init__(self):
        self._modules = []
        self._register_mythril_modules()

    def register_module(self, detection_module: DetectionModule):
        pass

    def get_detection_modules(self):
        pass

    def _register_mythril_modules(self):
        self._modules.extend([
            ArbitraryJump(),
            ArbitraryStorage(),
            DelegateCallModule(),
            PredictableDependenceModule(),
            DeprecatedOperationsModule(),
            EtherThief(),
            ReachableExceptionsModule(),
            ExternalCalls(),
            IntegerOverflowUnderflowModule(),
            MultipleSendsModule(),
            StateChange(),
            SuicideModule(),
            UncheckedRetvalModule(),
            UserAssertions(),
        ])
