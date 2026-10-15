import hashlib
import math

from tools.infra.proof_artifact_receipt import (
    build_candidate_receipt,
    verify_candidate_receipt,
)


BASE_RECORD = {
    "lean_file": "tmp/candidate.lean",
    "candidate_sha256": "a" * 64,
    "source_path": "lean/Example.lean",
    "source_snapshot_sha256": "b" * 64,
    "source_snapshot_current_sha256": "b" * 64,
    "source_context_changed": False,
    "toolchain": "leanprover/lean4:v4.34.1",
    "lakefile_sha256": "c" * 64,
    "lake_manifest_sha256": "d" * 64,
    "git_head": "e" * 40,
    "lean_check_returncode": 0,
    "lean_output_sha256": "f" * 64,
    "semantic_vacuity_returncode": 0,
    "semantic_vacuity_output_sha256": "1" * 64,
}


def test_receipt_is_deterministic_and_hash_verifies():
    first = build_candidate_receipt(BASE_RECORD)
    second = build_candidate_receipt(dict(BASE_RECORD))
    assert first == second
    assert verify_candidate_receipt(first)
    assert first["checks"]["axiomAudit"]["status"] == "not_requested"
    assert first["review"]["promotionAllowed"] is False


def test_receipt_digest_detects_mutation():
    receipt = build_candidate_receipt(BASE_RECORD)
    receipt["artifact"]["sha256"] = "0" * 64
    assert not verify_candidate_receipt(receipt)


def test_score_requires_explicit_finite_defect_and_policy():
    missing = build_candidate_receipt({**BASE_RECORD, "audit_defect": 0.5})
    assert missing["score"]["status"] == "unconfigured"
    valid = build_candidate_receipt({
        **BASE_RECORD,
        "audit_defect": 0.5,
        "audit_policy_version": "test-policy-v1",
    })
    assert valid["score"]["status"] == "policy_estimate"
    assert math.isclose(valid["score"]["value"], math.exp(-0.5))
    assert verify_candidate_receipt(valid)


def test_nonfinite_or_negative_defect_is_not_scored():
    for defect in (-1, float("nan"), float("inf"), True):
        receipt = build_candidate_receipt({
            **BASE_RECORD,
            "audit_defect": defect,
            "audit_policy_version": "test-policy-v1",
        })
        assert receipt["score"]["status"] == "unconfigured"


def test_axiom_audit_observation_is_carried_with_hash_and_target_names():
    output = "'Example.result' depends on axioms: [propext, Quot.sound]"
    receipt = build_candidate_receipt({
        **BASE_RECORD,
        "axiom_audit_status": "collected",
        "axiom_audit_declarations": ["Example.result"],
        "axiom_audit_returncode": 0,
        "axiom_audit_output": output,
        "axiom_audit_output_sha256": hashlib.sha256(output.encode()).hexdigest(),
    })
    audit = receipt["checks"]["axiomAudit"]
    assert audit["status"] == "collected"
    assert audit["declarations"] == ["Example.result"]
    assert audit["output"] == output
    assert verify_candidate_receipt(receipt)


def test_axiom_audit_cannot_be_marked_collected_without_lean_output():
    receipt = build_candidate_receipt({
        **BASE_RECORD,
        "axiom_audit_status": "collected",
        "axiom_audit_declarations": ["Example.result"],
        "axiom_audit_returncode": 0,
        "axiom_audit_output": "",
        "axiom_audit_output_sha256": "",
    })
    assert receipt["checks"]["axiomAudit"]["status"] == "failed"
    assert verify_candidate_receipt(receipt)
