from mythril.analysis.report import Report
from mythril.analysis import modules
import pkgutil


def fire_lasers(statespace):

    issues = []
    _modules = []
    
    for loader, name, is_pkg in pkgutil.walk_packages(modules.__path__):
        _modules.append(loader.find_module(name).load_module(name))

    for module in _modules:
        issues += module.execute(statespace)

    report = Report()

    if (len(issues)):

        for i in range(0, len(issues)):
            report.append_issue(issues[i])

        print(report.as_text())
