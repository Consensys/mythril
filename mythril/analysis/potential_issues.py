from mythril.analysis.report import Issue
from mythril.analysis.solver import get_transaction_sequence
from mythril.exceptions import UnsatError
from mythril.laser.ethereum.state.annotation import StateAnnotation
from mythril.laser.ethereum.state.global_state import GlobalState


class PotentialIssue:
    """Representation of a potential issue"""

    def __init__(
        self,
        contract,
        function_name,
        address,
        swc_id,
        title,
        bytecode,
        detector,
        severity=None,
        description_head="",
        description_tail="",
        constraints=None,
    ):
        """

        :param contract: The contract
        :param function_name: Function name where the issue is detected
        :param address: The address of the issue
        :param swc_id: Issue's corresponding swc-id
        :param title: Title
        :param bytecode: bytecode of the issue
        :param detector: The detector the potential issue belongs to
        :param gas_used: amount of gas used
        :param severity: The severity of the issue
        :param description_head: The top part of description
        :param description_tail: The bottom part of the description
        :param constraints: The non-path related constraints for the potential issue
        """
        self.title = title
        self.contract = contract
        self.function_name = function_name
        self.address = address
        self.description_head = description_head
        self.description_tail = description_tail
        self.severity = severity
        self.swc_id = swc_id
        self.bytecode = bytecode
        self.constraints = constraints or []
        self.detector = detector


class PotentialIssuesAnnotation(StateAnnotation):
    def __init__(self):
        self.potential_issues = []


def get_potential_issues_annotation(state: GlobalState) -> PotentialIssuesAnnotation:
    """
    Returns the potential issues annotation of the given global state, and creates one if
    one does not already exist.

    :param state: The global state
    :return:
    """
    for annotation in state.annotations:
        if isinstance(annotation, PotentialIssuesAnnotation):
            return annotation

    annotation = PotentialIssuesAnnotation()
    state.annotate(annotation)
    return annotation


def check_potential_issues(state: GlobalState) -> None:
    """
    Called at the end of a transaction, checks potential issues, and
    adds valid issues to the detector.

    :param state: The final global state of a transaction
    :return:
    """
    annotation = get_potential_issues_annotation(state)
    for potential_issue in annotation.potential_issues:
        try:
            transaction_sequence = get_transaction_sequence(
                state, state.mstate.constraints + potential_issue.constraints
            )
        except UnsatError:
            continue

        annotation.potential_issues.remove(potential_issue)
        potential_issue.detector._cache.add(potential_issue.address)
        potential_issue.detector._issues.append(
            Issue(
                contract=potential_issue.contract,
                function_name=potential_issue.function_name,
                address=potential_issue.address,
                title=potential_issue.title,
                bytecode=potential_issue.bytecode,
                swc_id=potential_issue.swc_id,
                gas_used=(state.mstate.min_gas_used, state.mstate.max_gas_used),
                severity=potential_issue.severity,
                description_head=potential_issue.description_head,
                description_tail=potential_issue.description_tail,
                transaction_sequence=transaction_sequence,
            )
        )
