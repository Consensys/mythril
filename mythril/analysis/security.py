from mythril.analysis.report import Report
from .modules import delegatecall_forward, unchecked_suicide, ether_send, unchecked_retval, delegatecall_to_dynamic, integer_underflow


def fire_lasers(statespace):

	issues = []

	issues += delegatecall_forward.execute(statespace)
	issues += delegatecall_to_dynamic.execute(statespace)
	issues += unchecked_suicide.execute(statespace)
	issues += unchecked_retval.execute(statespace)
	issues += ether_send.execute(statespace)
	issues += integer_underflow.execute(statespace)

	if (len(issues)):
		report = Report(issues)
		print(report.as_text())
