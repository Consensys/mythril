from mythril.analysis.report import Report
from mythril.analysis import modules
import pkgutil
import logging


def get_detection_modules(entrypoint, except_modules=None):
    except_modules = [] if except_modules is None else except_modules
    except_modules.append("base")  # always exclude base class file
    _modules = []

    for loader, name, _ in pkgutil.walk_packages(modules.__path__):
        module = loader.find_module(name).load_module(name)
        if (
            module.__name__ not in except_modules
            and module.detector.entrypoint == entrypoint
        ):
            _modules.append(module)

    logging.info("Found %s detection modules", len(_modules))
    return _modules


def fire_lasers(statespace, module_names=None):
    logging.info("Starting analysis")

    issues = []
    for module in get_detection_modules(entrypoint="post", except_modules=module_names):
        logging.info("Executing " + module.detector.name)
        issues += module.detector.execute(statespace)

    return issues
