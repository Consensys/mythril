from mythril.analysis.report import Report
from mythril.analysis import modules
import pkgutil
import logging


def fire_lasers(statespace, module_names=None):
    module_names = [] if module_names is None else module_names
    module_names.append("base")  # always exclude base class file
    issues = []
    _modules = []

    for loader, name, _ in pkgutil.walk_packages(modules.__path__):
        _modules.append(loader.find_module(name).load_module(name))

    logging.info("Starting analysis")

    for module in _modules:
        if module.__name__ not in module_names:
            logging.info("Executing " + module.detector.name)
            issues += module.detector.execute(statespace)

    return issues
