import json

import pytest

from tools.infra.hive_epistemic_bridge import MARKER, RECEIPT_SCHEMA, check_admission_output
from tools.infra.hive_workflow_policy import check_workflow_policy


TARGETS = ["Example.first", "Example.second"]


def receipt():
    return {
        "schema": RECEIPT_SCHEMA,
        "scheduler": "finite_dependency_compiler",
        "scope": "current_kernel_environment",
        "declarations": TARGETS,
        "reports": [
            {"name": name, "decision": "admitted", "blockers": [], "policyVersion": "test"}
            for name in TARGETS
        ],
    }


def execution(payload=None):
    return {
        "returncode": 0,
        "module": "Example",
        "stdout": "Example.lean:1:0: " + MARKER + json.dumps(payload if payload is not None else receipt()),
    }


def test_admission_normalizes_to_policy_not_promotion():
    result = check_admission_output(execution(), expected_declarations=TARGETS)
    assert result["ok"]
    assert not result["promotion_allowed"]
    assert [row["decl"] for row in result["records"]] == TARGETS
    assert all(row["authority_level"] == "policy" for row in result["records"])


@pytest.mark.parametrize("returncode", [None, False, "0", 1, -9])
def test_process_failure_cannot_be_hidden_by_receipt(returncode):
    output = execution()
    output["returncode"] = returncode
    assert not check_admission_output(output, expected_declarations=TARGETS)["ok"]


@pytest.mark.parametrize("stdout", ["", MARKER + "{", MARKER + "[]", MARKER + "{}\n" + MARKER + "{}"])
def test_missing_malformed_or_multiple_receipts_fail(stdout):
    assert not check_admission_output(
        {"returncode": 0, "stdout": stdout}, expected_declarations=TARGETS
    )["ok"]


@pytest.mark.parametrize("targets", [[], ["Example.first"], list(reversed(TARGETS)), TARGETS + TARGETS, [None]])
def test_independent_target_contract_is_required(targets):
    assert not check_admission_output(execution(), expected_declarations=targets)["ok"]


@pytest.mark.parametrize("field,value", [
    ("schema", "other"), ("scope", "archived"), ("scheduler", "heuristic"),
    ("reports", []), ("reports", [None]), ("declarations", list(reversed(TARGETS))),
])
def test_receipt_contract_is_fail_closed(field, value):
    payload = receipt()
    payload[field] = value
    assert not check_admission_output(execution(payload), expected_declarations=TARGETS)["ok"]


@pytest.mark.parametrize("field,value", [
    ("decision", "review"), ("decision", "blocked"), ("blockers", ["sorryAx"]),
    ("blockers", None), ("name", "Other.target"), ("policyVersion", ""),
])
def test_each_qms_report_must_match(field, value):
    payload = receipt()
    payload["reports"][0][field] = value
    assert not check_admission_output(execution(payload), expected_declarations=TARGETS)["ok"]


def test_os_gate_rejects_missing_evidence_even_with_other_gates_passed():
    report = check_workflow_policy(
        mode="checkpoint", before_files={}, after_files={},
        targeted_build_passed=True, project_build_passed=True, axiom_audit_passed=True,
        allow_unsound_markers=True, epistemic_required=True,
    )
    assert not report["ok"]
    assert report["violations"][0]["code"] == "epistemic_admission_required"


def test_os_gate_consumes_native_output_without_waiving_builds():
    report = check_workflow_policy(
        mode="checkpoint", before_files={}, after_files={},
        epistemic_execution=execution(), epistemic_declarations=TARGETS,
    )
    assert report["epistemic_check"]["ok"]
    assert not report["ok"]
    assert "checkpoint_missing_project_build" in {row["code"] for row in report["violations"]}
