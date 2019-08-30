import os
import time

from typing import List, Dict, Any

from mythril.analysis.report import Issue, Report
from mythril.solidity.soliditycontract import SolidityContract

from pythx import Client


def analyze(contracts: List[SolidityContract], analysis_mode: str = "quick") -> Report:
    """
    Analyze contracts via the MythX API.

    :param contracts: List of solidity contracts to analyze
    :param analysis_mode: The mode to submit the analysis request with. "quick" or "full" (default: "quick")
    :return: Report with analyzed contracts
    """
    assert analysis_mode in ("quick", "full"), "analysis_mode must be 'quick' or 'full'"

    c = Client(
        eth_address=os.environ.get(
            "MYTHX_ETH_ADDRESS", "0x0000000000000000000000000000000000000000"
        ),
        password=os.environ.get("MYTHX_PASSWORD", "trial"),
    )

    issues = []  # type: List[Issue]

    # TODO: Analyze multiple contracts asynchronously.
    for contract in contracts:
        source_codes = {}
        source_list = []
        sources = {}  # type: Dict[str, Any]
        main_source = None

        try:
            main_source = contract.input_file
            for solidity_file in contract.solidity_files:
                source_codes[solidity_file.filename] = solidity_file.data
            for filename in contract.solc_json["sources"].keys():
                sources[filename] = {}
                if source_codes[filename]:
                    sources[filename]["source"] = source_codes[filename]
                sources[filename]["ast"] = contract.solc_json["sources"][filename][
                    "ast"
                ]

                source_list.append(filename)

            source_list.sort(
                key=lambda fname: contract.solc_json["sources"][fname]["id"]
            )
        except AttributeError:
            # No solidity file
            pass

        assert contract.creation_code, "Creation bytecode must exist."
        resp = c.analyze(
            contract_name=contract.name,
            analysis_mode=analysis_mode,
            bytecode=contract.creation_code or None,
            deployed_bytecode=contract.code or None,
            sources=sources or None,
            main_source=main_source,
            source_list=source_list or None,
        )

        while not c.analysis_ready(resp.uuid):
            print(c.status(resp.uuid).analysis)
            time.sleep(5)

        for issue in c.report(resp.uuid):
            issue = Issue(
                contract=contract.name,
                function_name=None,
                address=issue.locations[0].source_map.components[0].offset,
                swc_id=issue.swc_id[4:],  # remove 'SWC-' prefix
                title=issue.swc_title,
                bytecode=contract.creation_code,
                severity=issue.severity.capitalize(),
                description_head=issue.description_short,
                description_tail=issue.description_long,
            )
            issue.add_code_info(contract)
            issues.append(issue)

    report = Report(contracts=contracts)
    for issue in issues:
        report.append_issue(issue)

    return report
