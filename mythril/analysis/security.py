from mythril.analysis.report import Report
from .modules import delegatecall_forward, unchecked_suicide


def fire_lasers(statespace):

	issues = []

	issues += delegatecall_forward.execute(statespace)
	issues += unchecked_suicide.execute(statespace)

	if (len(issues)):
		report = Report(issues)
		print(report.as_text())
