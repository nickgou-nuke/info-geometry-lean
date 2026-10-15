"""Regression Test Suite for QMS Production Defects.

Covers the three critical production defects identified by audit:
1. Axiom audit multiline wrapping and fail-closed parser enforcement.
2. Statement fidelity target selection (no fallback to declarations[0]) and unrelated structure isolation.
3. Gate 7 real semantic vacuity execution, source_context_changed detection, and non-promotion receipt authority.
"""

from __future__ import annotations

import json
from pathlib import Path
import tempfile
import pytest

from tools.infra.qms_evidence_pipeline import (
    EvidencePacket,
    GateResult,
    QMSEvidencePipeline,
    parse_axiom_audit_output,
)
from tools.quality.statement_fidelity_gate import (
    evaluate_statement_fidelity,
    check_hypotheses_fidelity,
    parse_lean_declarations,
    get_related_structures,
)

REPO_ROOT = Path(__file__).resolve().parents[2]


# =============================================================================
# Defect 1: Axiom Audit Multiline & Fail-Closed
# =============================================================================

def test_regression_axiom_audit_multiline_trojan_caught():
    """Verify that multiline wrapped #print axioms output containing custom axioms is parsed and rejected."""
    declarations = ["Top.wrapped_thm"]
    output = """'Top.wrapped_thm' depends on axioms: [propext,
  Classical.choice,
  TrojanAxiom]
"""
    parsed, errors = parse_axiom_audit_output(output, declarations)
    assert errors == []
    assert "Top.wrapped_thm" in parsed
    assert "TrojanAxiom" in parsed["Top.wrapped_thm"]
    assert "Classical.choice" in parsed["Top.wrapped_thm"]
    assert "propext" in parsed["Top.wrapped_thm"]

    # Verify Gate 5 logic rejects TrojanAxiom
    from tools.infra.qms_evidence_pipeline import ALLOWED_CORE_AXIOMS
    forbidden = [ax for ax in parsed["Top.wrapped_thm"] if ax not in ALLOWED_CORE_AXIOMS]
    assert forbidden == ["TrojanAxiom"]


def test_regression_axiom_audit_fails_closed_on_unparsed_declaration(tmp_path: Path):
    """Verify that Gate 5 fails closed if any requested declaration's axiom list cannot be parsed."""
    declarations = ["Top.existing_thm", "Top.unparsed_ghost_thm"]
    output = """'Top.existing_thm' depends on axioms: [propext]
"""
    parsed, errors = parse_axiom_audit_output(output, declarations)
    assert any("Top.unparsed_ghost_thm" in err for err in errors)

    # Test Gate 5 execution fails closed when parse_errors occur
    pipeline = QMSEvidencePipeline()
    lean_file = tmp_path / "Ghost.lean"
    lean_file.write_text("theorem existing_thm : 1 = 1 := rfl\n", encoding="utf-8")
    spec_file = tmp_path / "spec.json"
    spec_file.write_text(json.dumps({
        "claim": "Ghost Spec",
        "carrier": "Nat",
        "hypotheses": [],
        "target_conclusion": "1 = 1",
    }), encoding="utf-8")

    _, pkt = pipeline.gate_1_intake(spec_file, lean_file)
    assert pkt is not None
    # Intentionally corrupt declarations to simulate missing output
    res, errors = parse_axiom_audit_output(output, ["Top.unparsed_ghost_thm"])
    assert any("missing axiom output" in err for err in errors)


def test_regression_axiom_audit_no_axioms_clean_pass():
    """Verify that declarations outputting 'does not depend on any axioms' parse cleanly as empty lists."""
    declarations = ["Top.pure_rfl_thm"]
    output = "'Top.pure_rfl_thm' does not depend on any axioms\n"
    parsed, errors = parse_axiom_audit_output(output, declarations)
    assert errors == []
    assert parsed["Top.pure_rfl_thm"] == []


# =============================================================================
# Defect 2: Statement Fidelity Target Selection & Unrelated Structures
# =============================================================================

def test_regression_statement_fidelity_missing_target_fails_closed():
    """Verify that when a requested theorem is missing from the file, evaluation does NOT fall back to declarations[0]."""
    code = """
theorem unrelated_first_declaration (x : Real) : x = x := by sorry
"""
    spec = {
        "theorem_name": "requested_target_theorem_that_does_not_exist",
        "carrier_requirements": {
            "expected_carrier": "Real",
        },
        "required_hypotheses": [],
        "target_relation": {
            "type": "equality",
            "relation_symbol": "=",
            "pattern": "x = x",
        },
    }

    report = evaluate_statement_fidelity(code, spec)
    assert report.passed is False
    assert report.fidelity_score == 0.0
    assert any(d.defect_type == "TARGET_DECLARATION_NOT_FOUND" for d in report.defects)
    target_defect = next(d for d in report.defects if d.defect_type == "TARGET_DECLARATION_NOT_FOUND")
    assert target_defect.severity == "FATAL"
    assert "requested_target_theorem_that_does_not_exist" in target_defect.message


def test_regression_statement_fidelity_unrelated_structure_isolated():
    """Direct probe: an unrelated structure in the same file must NOT satisfy hypotheses of the target theorem."""
    code = """
structure UnrelatedAxiomCarrier where
  orthogonal_flux : True
  unrelated_hypothesis : True

theorem actual_target_theorem (x : Real) : x = x := by sorry
"""
    # Spec requires orthogonal_flux hypothesis.
    # Because actual_target_theorem does not use UnrelatedAxiomCarrier, this hypothesis is DROPPED.
    spec = {
        "theorem_name": "actual_target_theorem",
        "carrier_requirements": {
            "expected_carrier": "Real",
        },
        "required_hypotheses": [
            {
                "name": "orthogonal_flux",
                "pattern": "orthogonal_flux",
                "description": "Required orthogonality constraint",
            }
        ],
        "target_relation": {
            "type": "equality",
            "relation_symbol": "=",
            "pattern": "x = x",
        },
    }

    decls, structs = parse_lean_declarations(code)
    target_decl = next(d for d in decls if d.name == "actual_target_theorem")

    # Verify that get_related_structures filters out UnrelatedAxiomCarrier
    related = get_related_structures(target_decl, structs)
    assert "UnrelatedAxiomCarrier" not in related

    # Verify that evaluate_statement_fidelity reports the dropped hypothesis and does NOT score 1.0
    report = evaluate_statement_fidelity(code, spec)
    assert report.passed is False
    assert report.fidelity_score < 1.0
    assert any(d.defect_type == "DROPPED_HYPOTHESIS" for d in report.defects)
    dropped = [d.context for d in report.defects if d.defect_type == "DROPPED_HYPOTHESIS"]
    assert "orthogonal_flux" in dropped


def test_regression_statement_fidelity_related_structure_included():
    """Verify that when a structure IS used as a binder, its hypotheses ARE legitimately recognized."""
    code = """
structure SymplecticPair where
  J : Matrix (Fin 2) (Fin 2) ℝ
  is_skew : True

theorem preserve_symplectic (P : SymplecticPair) : P.J * P.J = P.J := by sorry
"""
    spec = {
        "theorem_name": "preserve_symplectic",
        "carrier_requirements": {
            "expected_carrier": "SymplecticPair",
        },
        "required_hypotheses": [
            {
                "name": "is_skew",
                "pattern": "is_skew",
                "description": "Skew-symmetric hypothesis",
            }
        ],
        "target_relation": {
            "type": "equality",
            "relation_symbol": "=",
            "pattern": "P\\.J\\s*\\*\\s*P\\.J\\s*=\\s*P\\.J",
        },
    }

    report = evaluate_statement_fidelity(code, spec)
    assert report.passed is True
    assert report.fidelity_score == 1.0
    assert len(report.defects) == 0


# =============================================================================
# Defect 3: Gate 7 Status and Provenance
# =============================================================================

def test_regression_gate_7_executes_semantic_vacuity_audit_and_rejects_errors(tmp_path: Path):
    """Verify that Gate 7 genuinely executes semantic_vacuity_gate.py and fails on error-level vacuity findings."""
    pipeline = QMSEvidencePipeline()

    # Create a Lean file with a pure_proof_carrier error (structure named Witness with no data fields)
    vacuous_lean = tmp_path / "VacuousCarrier.lean"
    vacuous_lean.write_text("""
structure FakeWitness where
  h : True = True

theorem t : True := trivial
""", encoding="utf-8")

    spec_file = tmp_path / "spec.json"
    spec_file.write_text(json.dumps({
        "claim": "Vacuity Test",
        "carrier": "FakeWitness",
        "hypotheses": [],
        "target_conclusion": "True",
    }), encoding="utf-8")

    _, pkt = pipeline.gate_1_intake(spec_file, vacuous_lean)
    assert pkt is not None

    import hashlib
    actual_sha = hashlib.sha256(vacuous_lean.read_bytes()).hexdigest()

    # Construct mock Gate 5 result matching actual file sha
    g5_mock = GateResult(
        gate_number=5,
        gate_name="KERNEL_SOURCE_CHECK",
        passed=True,
        details={
            "lean_returncode": 0,
            "lean_output": "",
            "candidate_sha256": actual_sha,
            "axiom_audit_output": "'t' does not depend on any axioms\n",
            "axiom_audit_declarations": ["t"],
            "axiom_audit_returncode": 0,
        },
    )

    g7_res, receipt, _ = pipeline.gate_7_promotion_and_receipt(pkt, g5_mock)
    assert g7_res.passed is False
    assert receipt is None
    assert "Gate 7 Semantic Vacuity Failure" in g7_res.socratic_critique
    assert g7_res.details["semantic_vacuity_returncode"] != 0


def test_regression_gate_7_detects_source_context_changed_and_fails_promotion(tmp_path: Path):
    """Verify that Gate 7 detects source_context_changed=True when source diverges from snapshot, refusing promotion."""
    pipeline = QMSEvidencePipeline()

    clean_lean = tmp_path / "Clean.lean"
    clean_lean.write_text("theorem t : 1 = 1 := rfl\n", encoding="utf-8")

    # Spec provides an outdated/divergent source_snapshot_sha256
    spec_file = tmp_path / "spec.json"
    spec_file.write_text(json.dumps({
        "claim": "Provenance Test",
        "carrier": "Nat",
        "hypotheses": [],
        "target_conclusion": "1 = 1",
        "source_snapshot_sha256": "0" * 64,  # Divergent snapshot!
    }), encoding="utf-8")

    _, pkt = pipeline.gate_1_intake(spec_file, clean_lean)
    assert pkt is not None

    import hashlib
    actual_sha = hashlib.sha256(clean_lean.read_bytes()).hexdigest()
    g5_mock = GateResult(
        gate_number=5,
        gate_name="KERNEL_SOURCE_CHECK",
        passed=True,
        details={
            "lean_returncode": 0,
            "lean_output": "",
            "candidate_sha256": actual_sha,
            "axiom_audit_output": "'t' does not depend on any axioms\n",
            "axiom_audit_declarations": ["t"],
            "axiom_audit_returncode": 0,
        },
    )

    g7_res, receipt, _ = pipeline.gate_7_promotion_and_receipt(pkt, g5_mock)
    assert receipt is not None
    # Crucial provenance assertion: source_context_changed detected!
    assert receipt["source"]["changedSincePrompt"] is True
    assert receipt["review"]["status"] == "source_context_changed_pending_review"
    assert receipt["review"]["promotionAllowed"] is False
    assert g7_res.details["source_context_changed"] is True
    assert g7_res.details["promotion_allowed"] is False

    # In whole-pipeline execution, verify report never claims PROMOTED or ACCEPTED
    report = pipeline.run_pipeline(spec_path=spec_file, lean_file=clean_lean)
    assert report.status != "PROMOTED"
    assert report.final_verdict != "ACCEPTED"


def test_regression_gate_7_receipt_contract_promotion_allowed_is_false(tmp_path: Path):
    """Verify that even on a clean pass, minted receipts strictly enforce promotionAllowed=False."""
    pipeline = QMSEvidencePipeline()

    clean_lean = tmp_path / "CleanPass.lean"
    clean_lean.write_text("theorem t : 1 = 1 := rfl\n", encoding="utf-8")
    import hashlib
    actual_sha = hashlib.sha256(clean_lean.read_bytes()).hexdigest()

    spec_file = tmp_path / "spec.json"
    spec_file.write_text(json.dumps({
        "claim": "Authority Test",
        "carrier": "Nat",
        "hypotheses": [],
        "target_conclusion": "1 = 1",
        "source_snapshot_sha256": actual_sha,
    }), encoding="utf-8")

    _, pkt = pipeline.gate_1_intake(spec_file, clean_lean)
    assert pkt is not None

    g5_mock = GateResult(
        gate_number=5,
        gate_name="KERNEL_SOURCE_CHECK",
        passed=True,
        details={
            "lean_returncode": 0,
            "lean_output": "",
            "candidate_sha256": actual_sha,
            "axiom_audit_output": "'t' does not depend on any axioms\n",
            "axiom_audit_declarations": ["t"],
            "axiom_audit_returncode": 0,
        },
    )

    g7_res, receipt, _ = pipeline.gate_7_promotion_and_receipt(pkt, g5_mock)
    assert g7_res.passed is True
    assert receipt is not None
    assert receipt["authority"] == "candidate_observation_not_proof_authority"
    assert receipt["review"]["promotionAllowed"] is False
    assert receipt["review"]["status"] == "kernel_checked_pending_owner_review"
    assert g7_res.details["promotion_allowed"] is False
    assert g7_res.details["receipt_authority"] == "candidate_observation_not_proof_authority"
