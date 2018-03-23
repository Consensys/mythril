from mythril.analysis.report import Report
from mythril.analysis import modules
import pkgutil
import logging


def fire_lasers(statespace, module_names=None):

    issues = []
    _modules = []

    for loader, name, is_pkg in pkgutil.walk_packages(modules.__path__):
        _modules.append(loader.find_module(name).load_module(name))

    logging.info("Starting analysis")

    for module in _modules:
        if not module_names or module.__name__ in module_names:
            logging.info("Executing " + str(module))
            issues += module.execute(statespace)

    return issues
