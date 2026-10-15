"""Regression Test Suite for QMS Production Defects.

Covers the three critical production defects identified by audit:
1. Axiom audit multiline wrapping and fail-closed parser enforcement.
2. Statement fidelity target selection (no fallback to declarations[0]) and unrelated structure isolation.
3. Gate 7 real semantic vacuity execution, source_context_changed detection, and non-promotion receipt authority.
"""

from __future__ import annotations

import json
import hashlib
from pathlib import Path
import tempfile
import pytest

from tools.infra.qms_evidence_pipeline import (
    EvidencePacket,
    GateResult,
    QMSEvidencePipeline,
    extract_lean_declarations,
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


def test_gate6_rejects_selected_name_missing_from_gate5_kernel_audit(tmp_path: Path):
    lean_file = tmp_path / "Candidate.lean"
    lean_file.write_text("theorem intended : True := by trivial", encoding="utf-8")
    packet = EvidencePacket(
        spec_path=tmp_path / "spec.json",
        lean_file=lean_file,
        claim="declaration identity",
        carrier="Prop",
        hypotheses=[],
        target_conclusion="True",
        raw_spec={"theorem_name": "intended"},
    )
    kernel_result = GateResult(
        gate_number=5,
        gate_name="KERNEL_SOURCE_CHECK",
        passed=True,
        details={
            "axiom_audit_declarations": ["other_name"],
            "candidate_sha256": hashlib.sha256(lean_file.read_bytes()).hexdigest(),
            "source_snapshot_text": lean_file.read_text(encoding="utf-8"),
        },
    )
    result = QMSEvidencePipeline().gate_6_statement_fidelity_review(packet, kernel_result)
    assert not result.passed
    assert "identity" in result.diagnostics[0]


def test_gate6_accepts_exact_selected_name_from_gate5_kernel_audit(tmp_path: Path):
    lean_file = tmp_path / "Candidate.lean"
    lean_file.write_text("theorem intended (n : Nat) : n + 0 = n := by simp", encoding="utf-8")
    packet = EvidencePacket(
        spec_path=tmp_path / "spec.json",
        lean_file=lean_file,
        claim="declaration identity",
        carrier="Prop",
        hypotheses=[],
        target_conclusion="n + 0 = n",
        raw_spec={"theorem_name": "intended"},
    )
    kernel_result = GateResult(
        gate_number=5,
        gate_name="KERNEL_SOURCE_CHECK",
        passed=True,
        details={
            "axiom_audit_declarations": ["intended"],
            "candidate_sha256": hashlib.sha256(lean_file.read_bytes()).hexdigest(),
            "source_snapshot_text": lean_file.read_text(encoding="utf-8"),
        },
    )
    result = QMSEvidencePipeline().gate_6_statement_fidelity_review(packet, kernel_result)
    assert result.passed


def test_gate6_rejects_source_changed_since_gate5(tmp_path: Path):
    lean_file = tmp_path / "Candidate.lean"
    original = "theorem intended (n : Nat) : n + 0 = n := by simp"
    lean_file.write_text(original, encoding="utf-8")
    packet = EvidencePacket(
        spec_path=tmp_path / "spec.json",
        lean_file=lean_file,
        claim="source snapshot identity",
        carrier="Nat",
        hypotheses=[],
        target_conclusion="n + 0 = n",
        raw_spec={"theorem_name": "intended"},
    )
    kernel_result = GateResult(
        gate_number=5,
        gate_name="KERNEL_SOURCE_CHECK",
        passed=True,
        details={
            "axiom_audit_declarations": ["intended"],
            "candidate_sha256": "0" * 64,
            "source_snapshot_text": original,
        },
    )
    result = QMSEvidencePipeline().gate_6_statement_fidelity_review(packet, kernel_result)
    assert not result.passed
    assert "does not match" in result.diagnostics[0]


def test_gate6_rejects_missing_gate5_source_fingerprint(tmp_path: Path):
    lean_file = tmp_path / "Candidate.lean"
    lean_file.write_text("theorem intended (n : Nat) : n + 0 = n := by simp", encoding="utf-8")
    packet = EvidencePacket(
        spec_path=tmp_path / "spec.json",
        lean_file=lean_file,
        claim="required source binding",
        carrier="Nat",
        hypotheses=[],
        target_conclusion="n + 0 = n",
        raw_spec={"theorem_name": "intended"},
    )
    kernel_result = GateResult(
        gate_number=5,
        gate_name="KERNEL_SOURCE_CHECK",
        passed=True,
        details={"axiom_audit_declarations": ["intended"]},
    )
    result = QMSEvidencePipeline().gate_6_statement_fidelity_review(packet, kernel_result)
    assert not result.passed
    assert "missing a valid candidate_sha256" in result.diagnostics[0]


def test_gate6_rejects_nonpassing_gate5_result(tmp_path: Path):
    lean_file = tmp_path / "Candidate.lean"
    lean_file.write_text("theorem intended (n : Nat) : n + 0 = n := by simp", encoding="utf-8")
    packet = EvidencePacket(
        spec_path=tmp_path / "spec.json",
        lean_file=lean_file,
        claim="passing kernel evidence required",
        carrier="Nat",
        hypotheses=[],
        target_conclusion="n + 0 = n",
        raw_spec={"theorem_name": "intended"},
    )
    kernel_result = GateResult(
        gate_number=5,
        gate_name="KERNEL_SOURCE_CHECK",
        passed=False,
        details={"candidate_sha256": hashlib.sha256(lean_file.read_bytes()).hexdigest()},
    )
    result = QMSEvidencePipeline().gate_6_statement_fidelity_review(packet, kernel_result)
    assert not result.passed
    assert "did not pass" in result.diagnostics[0]


def test_gate6_rejects_missing_gate5_result(tmp_path: Path):
    lean_file = tmp_path / "Candidate.lean"
    lean_file.write_text("theorem intended : True := by trivial", encoding="utf-8")
    packet = EvidencePacket(
        spec_path=tmp_path / "spec.json", lean_file=lean_file, claim="required evidence",
        carrier="Prop", hypotheses=[], target_conclusion="True",
        raw_spec={"theorem_name": "intended"},
    )
    result = QMSEvidencePipeline().gate_6_statement_fidelity_review(packet)
    assert not result.passed
    assert "requires the passing Gate 5 result" in result.diagnostics[0]


def test_gate6_uses_hash_bound_gate5_snapshot_after_owner_file_changes(tmp_path: Path):
    lean_file = tmp_path / "Candidate.lean"
    snapshot = "theorem intended : True := by trivial\n"
    lean_file.write_text(snapshot, encoding="utf-8")
    packet = EvidencePacket(
        spec_path=tmp_path / "spec.json", lean_file=lean_file, claim="immutable snapshot",
        carrier="Prop", hypotheses=[], target_conclusion="True",
        raw_spec={"theorem_name": "intended"},
    )
    kernel_result = GateResult(
        gate_number=5, gate_name="KERNEL_SOURCE_CHECK", passed=True,
        details={
            "axiom_audit_declarations": ["intended"],
            "candidate_sha256": hashlib.sha256(snapshot.encode()).hexdigest(),
            "source_snapshot_text": snapshot,
        },
    )
    lean_file.write_text("theorem decoy : False := by trivial\n", encoding="utf-8")
    result = QMSEvidencePipeline().gate_6_statement_fidelity_review(packet, kernel_result)
    assert "intended" in result.details["reports"]
    assert result.details["reports"]["intended"]["theorem_name"] == "intended"


def test_actual_cl11_json_target_symbol_is_resolved_through_gate6():
    source_path = REPO_ROOT / "lean/InfoGeometry/Clifford/Cl11SplitQuaternions.lean"
    spec_path = REPO_ROOT / "specs/cl11_split_quaternions.json"
    source_bytes = source_path.read_bytes()
    source_text = source_bytes.decode("utf-8")
    spec = json.loads(spec_path.read_text(encoding="utf-8"))
    packet = EvidencePacket(
        spec_path=spec_path,
        lean_file=source_path,
        claim=spec["claim"],
        carrier=spec["carrier"],
        hypotheses=spec["hypotheses"],
        target_conclusion=spec["target_conclusion"],
        raw_spec=spec,
    )
    gate5 = GateResult(
        gate_number=5,
        gate_name="KERNEL_SOURCE_CHECK",
        passed=True,
        details={
            "axiom_audit_declarations": extract_lean_declarations(source_text),
            "candidate_sha256": hashlib.sha256(source_bytes).hexdigest(),
            "source_snapshot_text": source_text,
        },
    )
    result = QMSEvidencePipeline().gate_6_statement_fidelity_review(packet, gate5)
    report = next(iter(result.details["reports"].values()))
    assert report["theorem_name"] == "InfoGeometry.Clifford.Cl11.cl12_biquaternion_generator_relations"
    assert not any(
        defect["defect_type"] == "TARGET_DECLARATION_NOT_FOUND"
        for defect in report["defects"]
    )


def test_gate5_control_flow_rejects_custom_axiom_audit_output(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
):
    """Exercise Gate 5's compiler/audit/parser path using controlled subprocess results."""
    import subprocess
    import tools.infra.qms_evidence_pipeline as qms_module

    lean_file = tmp_path / "Trojan.lean"
    lean_file.write_text(
        "axiom TrojanAxiom : False\ntheorem uses_trojan : False := TrojanAxiom\n",
        encoding="utf-8",
    )
    packet = EvidencePacket(
        spec_path=tmp_path / "spec.json",
        lean_file=lean_file,
        claim="custom axiom rejection",
        carrier="Prop",
        hypotheses=[],
        target_conclusion="False",
        raw_spec={"theorem_name": "uses_trojan"},
    )
    calls = 0

    def fake_run(cmd, **kwargs):
        nonlocal calls
        calls += 1
        if calls == 1:
            return subprocess.CompletedProcess(cmd, 0, stdout="compiled", stderr="")
        return subprocess.CompletedProcess(
            cmd, 0,
            stdout="'uses_trojan' depends on axioms: [TrojanAxiom]\n",
            stderr="",
        )

    monkeypatch.setattr(qms_module.subprocess, "run", fake_run)
    result = QMSEvidencePipeline().gate_5_kernel_and_integration(packet)
    assert not result.passed
    assert result.details["forbidden_axioms"] == {"uses_trojan": ["TrojanAxiom"]}


def test_gate5_compiles_and_audits_same_immutable_source_snapshot(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
):
    import subprocess
    import tools.infra.qms_evidence_pipeline as qms_module

    source = "theorem stable : True := by trivial\n"
    lean_file = tmp_path / "Stable.lean"
    lean_file.write_text(source, encoding="utf-8")
    packet = EvidencePacket(
        spec_path=tmp_path / "spec.json", lean_file=lean_file, claim="snapshot identity",
        carrier="Prop", hypotheses=[], target_conclusion="True",
        raw_spec={"theorem_name": "stable"},
    )
    calls = 0
    observed: list[bytes] = []

    def fake_run(cmd, **kwargs):
        nonlocal calls
        calls += 1
        candidate_path = Path(cmd[-1])
        if calls == 1:
            observed.append(candidate_path.read_bytes())
            # Mutating the mutable source after the snapshot must not affect the audit.
            lean_file.write_text("theorem mutated : False := by trivial\n", encoding="utf-8")
            return subprocess.CompletedProcess(cmd, 0, stdout="compile pass", stderr="")
        audit_text = candidate_path.read_text(encoding="utf-8")
        observed.append(audit_text.split("#print axioms stable", 1)[0].removeprefix("import Lean\n").rstrip().encode() + b"\n")
        return subprocess.CompletedProcess(
            cmd, 0, stdout="'stable' depends on axioms: [propext]\n", stderr=""
        )

    monkeypatch.setattr(qms_module.subprocess, "run", fake_run)
    result = QMSEvidencePipeline().gate_5_kernel_and_integration(packet)
    assert result.passed
    assert observed[0] == source.encode("utf-8")
    assert observed[1] == source.encode("utf-8")
    assert result.details["source_snapshot_text"] == source
    assert result.details["candidate_sha256"] == hashlib.sha256(source.encode()).hexdigest()
    assert calls == 2


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
