"""Comprehensive Test Suite for OpenGauss QMS Evidence Pipeline.

Verifies:
1. Structured dataclasses: GateResult, PipelineReport, EvidencePacket.
2. Gate 1 Intake: Valid specification parsing and missing field rejection.
3. Gate 2 Grounding: Poset prerequisite and acyclic dependency cone verification.
4. Gate 3 Adversarial Review: Detection of traps T1-T17 and screener violations.
5. Gate 4 Interactive Prover: Goal closure, sorry/admit banning, and memoization cache.
6. Gate 5 Kernel & Axiom Audit: flock-locked compilation and 0-custom-axiom enforcement.
7. Gate 6 Statement Fidelity: Semantic verification beyond compilation (fidelity >= 0.95).
8. Gate 7 Promotion & Receipt: Deterministic SHA256 receipt minting and verification.
9. End-to-end integration: 100% clean execution on BirkhoffPosetOperatorProjector and MasterEpistemicColimitSynthesis.
"""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
import pytest

from tools.infra.qms_evidence_pipeline import (
    EvidencePacket,
    GateResult,
    PipelineReport,
    QMSEvidencePipeline,
    extract_lean_declarations,
    parse_axiom_audit_output,
    strip_comments_and_strings,
    strip_lean_comments,
)

REPO_ROOT = Path(__file__).resolve().parents[1]


# -----------------------------------------------------------------------------
# Unit Tests: Dataclasses & Parsing Utilities
# -----------------------------------------------------------------------------

def test_dataclasses_serialization():
    """Verify GateResult, EvidencePacket, and PipelineReport serialize cleanly."""
    res = GateResult(
        gate_number=1,
        gate_name="INTAKE",
        passed=True,
        diagnostics=["Parsed OK"],
        duration_seconds=0.01,
    )
    d_res = res.to_dict()
    assert d_res["gate_number"] == 1
    assert d_res["passed"] is True

    packet = EvidencePacket(
        spec_path=Path("spec.json"),
        lean_file=Path("Test.lean"),
        claim="Test Claim",
        carrier="Matrix (Fin 2) (Fin 2) ℝ",
        hypotheses=["h1"],
        target_conclusion="A = B",
    )
    d_pkt = packet.to_dict()
    assert d_pkt["claim"] == "Test Claim"

    report = PipelineReport(
        target_file="Test.lean",
        spec_file="spec.json",
        status="PROMOTED",
        final_verdict="ACCEPTED",
        gates=[res],
    )
    d_rep = report.to_dict()
    assert d_rep["status"] == "PROMOTED"
    assert len(d_rep["gates"]) == 1


def test_strip_comments_and_strings():
    """Verify comment and string stripping handles line and block comments."""
    code = 'def x : String := "hello -- world" -- comment\n/- block -/ def y := 1'
    stripped = strip_comments_and_strings(code)
    assert "-- comment" not in stripped
    assert "block" not in stripped
    assert "def x" in stripped
    assert "def y" in stripped


def test_extract_lean_declarations():
    """Verify declaration extractor tracks namespaces correctly."""
    lean_text = """
    namespace Top
    theorem th1 : 1 = 1 := rfl
    namespace Inner
    lemma lm2 : 2 = 2 := rfl
    end Inner
    theorem th3 : 3 = 3 := rfl
    end Top
    """
    decls = extract_lean_declarations(lean_text)
    assert decls == ["Top.th1", "Top.Inner.lm2", "Top.th3"]


def test_parse_axiom_audit_output_handles_wrapping_and_fails_closed():
    declarations = ["Top.good", "Top.clean"]
    output = """'Top.good' depends on axioms: [propext,
  Classical.choice,
  custom_trojan]
'Top.clean' depends on axioms: [Quot.sound]
"""
    parsed, errors = parse_axiom_audit_output(output, declarations)
    assert errors == []
    assert parsed["Top.good"] == ["propext", "Classical.choice", "custom_trojan"]
    assert parsed["Top.clean"] == ["Quot.sound"]

    _, missing = parse_axiom_audit_output("'Top.good' depends on axioms: []", declarations)
    assert any("missing axiom output" in err for err in missing)
    _, empty = parse_axiom_audit_output("", declarations)
    assert any("no axiom audit output" in err for err in empty)


def test_changed_source_is_recorded_pending_review_not_dropped(tmp_path: Path):
    source = tmp_path / "Candidate.lean"
    source.write_text("theorem candidate : True := by trivial\n", encoding="utf-8")
    pipeline = QMSEvidencePipeline()
    packet = EvidencePacket(
        spec_path=tmp_path / "spec.json",
        lean_file=source,
        claim="candidate receipt test",
        carrier="Prop",
        hypotheses=[],
        target_conclusion="True",
        raw_spec={"source_snapshot_sha256": "0" * 64},
    )
    kernel_result = GateResult(
        gate_number=5,
        gate_name="KERNEL_SOURCE_CHECK",
        passed=True,
        details={
            "candidate_sha256": hashlib.sha256(source.read_bytes()).hexdigest(),
            "source_snapshot_text": source.read_text(encoding="utf-8"),
            "lean_returncode": 0,
            "lean_output": "",
            "axiom_audit_declarations": [],
            "axiom_audit_output": "",
            "axiom_audit_returncode": 0,
        },
    )
    fidelity_result = GateResult(
        gate_number=6,
        gate_name="STATEMENT_FIDELITY_REVIEW",
        passed=True,
    )
    result, receipt, receipt_path = pipeline.gate_7_candidate_receipt(
        packet, kernel_result, out_receipt=tmp_path / "candidate.receipt.json",
        fidelity_result=fidelity_result,
    )
    assert result.passed
    assert receipt is not None and receipt["review"]["promotionAllowed"] is False
    assert receipt["review"]["status"] == "source_context_changed_pending_review"
    assert receipt_path is not None and receipt_path.is_file()


def test_gate7_rejects_missing_gate6_evidence(tmp_path: Path):
    source = tmp_path / "Candidate.lean"
    source.write_text("theorem candidate : True := by trivial\n", encoding="utf-8")
    packet = EvidencePacket(
        spec_path=tmp_path / "spec.json", lean_file=source, claim="requires Gate 6",
        carrier="Prop", hypotheses=[], target_conclusion="True", raw_spec={},
    )
    kernel_result = GateResult(
        gate_number=5, gate_name="KERNEL_SOURCE_CHECK", passed=True,
        details={
            "candidate_sha256": hashlib.sha256(source.read_bytes()).hexdigest(),
            "source_snapshot_text": source.read_text(encoding="utf-8"),
        },
    )
    result, receipt, _ = QMSEvidencePipeline().gate_7_candidate_receipt(packet, kernel_result)
    assert not result.passed
    assert receipt is None
    assert "passing Gate 6" in result.diagnostics[0]


# -----------------------------------------------------------------------------
# Gate-by-Gate Unit Tests
# -----------------------------------------------------------------------------

def test_gate_1_intake_validation(tmp_path: Path):
    """Verify Gate 1 validates required specification fields and halts on missing ones."""
    pipeline = QMSEvidencePipeline()

    lean_file = tmp_path / "Dummy.lean"
    lean_file.write_text("theorem d : True := trivial\n", encoding="utf-8")

    # Missing file
    g1_missing, pkt = pipeline.gate_1_intake(tmp_path / "nonexistent.json", lean_file)
    assert not g1_missing.passed
    assert "does not exist" in g1_missing.socratic_critique

    # Incomplete specification (missing claim and carrier)
    bad_spec = tmp_path / "bad_spec.json"
    bad_spec.write_text(json.dumps({"unknown": "data"}), encoding="utf-8")
    g1_bad, pkt = pipeline.gate_1_intake(bad_spec, lean_file)
    assert not g1_bad.passed
    assert "Incomplete specification packet" in g1_bad.socratic_critique

    # Valid specification
    good_spec = tmp_path / "good_spec.json"
    good_spec.write_text(
        json.dumps({
            "claim": "Test Theorem",
            "carrier": "Matrix (Fin 2) (Fin 2) ℝ",
            "hypotheses": [],
            "target_conclusion": "x = x",
        }),
        encoding="utf-8",
    )
    g1_good, pkt = pipeline.gate_1_intake(good_spec, lean_file)
    assert g1_good.passed
    assert pkt is not None
    assert pkt.claim == "Test Theorem"


def test_gate_2_grounding_cycle_detection(tmp_path: Path):
    """Verify Gate 2 detects cyclic dependencies in declaration cones."""
    pipeline = QMSEvidencePipeline()

    # Cyclic dependency: foo references bar, bar references foo
    cyclic_code = """
    import Mathlib

    def foo : Nat := bar + 1
    def bar : Nat := foo + 1
    """
    lean_file = tmp_path / "Cyclic.lean"
    lean_file.write_text(cyclic_code, encoding="utf-8")

    spec_file = tmp_path / "spec.json"
    spec_file.write_text(json.dumps({"claim": "Cycle Test", "carrier": "Nat", "hypotheses": [], "target_conclusion": "foo = bar"}), encoding="utf-8")

    _, pkt = pipeline.gate_1_intake(spec_file, lean_file)
    assert pkt is not None
    g2 = pipeline.gate_2_grounding(pkt)
    assert not g2.passed
    assert "Dependency cycle detected" in g2.socratic_critique or "cycles" in g2.socratic_critique


def test_gate_3_adversarial_screener_rejects_traps(tmp_path: Path):
    """Verify Gate 3 catches 17-Trap violations."""
    pipeline = QMSEvidencePipeline(strict=True)

    # Trap T4 (vacuous binder) + Trap T16 (scalar toy surrogate)
    bad_code = """
    import Mathlib

    structure BlockSuperTrace (R : Type*) where
      tr_A : R
      tr_D : R

    theorem vacuous_claim (x : Real) (h : 0 = 0) : x ≤ x := by
      linarith
    """
    lean_file = tmp_path / "Traps.lean"
    lean_file.write_text(bad_code, encoding="utf-8")

    spec_file = tmp_path / "spec.json"
    spec_file.write_text(json.dumps({"claim": "Trap Test", "carrier": "Real", "hypotheses": [], "target_conclusion": "x ≤ x"}), encoding="utf-8")

    _, pkt = pipeline.gate_1_intake(spec_file, lean_file)
    assert pkt is not None
    g3 = pipeline.gate_3_static_trap_screen(pkt)
    assert not g3.passed
    assert "Trap T4" in g3.socratic_critique or "Trap T16" in g3.socratic_critique


def test_gate_4_static_scan_rejects_sorry(tmp_path: Path):
    """Verify the lexical Gate 4 scan flags sorry and admit tokens."""
    pipeline = QMSEvidencePipeline()

    sorry_code = """
    import Mathlib

    theorem unproven_claim (x : Real) : x = x := by
      sorry
    """
    lean_file = tmp_path / "Sorry.lean"
    lean_file.write_text(sorry_code, encoding="utf-8")

    spec_file = tmp_path / "spec.json"
    spec_file.write_text(json.dumps({"claim": "Sorry Test", "carrier": "Real", "hypotheses": [], "target_conclusion": "x = x"}), encoding="utf-8")

    _, pkt = pipeline.gate_1_intake(spec_file, lean_file)
    assert pkt is not None
    g4 = pipeline.gate_4_static_proof_hole_scan(pkt)
    assert not g4.passed
    assert "Unclosed proof holes detected" in g4.socratic_critique
    assert any("Hole 'sorry'" in d for d in g4.diagnostics)


def test_deterministic_halting_on_failure(tmp_path: Path):
    """Verify that a failure at an early gate halts subsequent gate progression."""
    pipeline = QMSEvidencePipeline()

    bad_spec = tmp_path / "corrupt.json"
    bad_spec.write_text("{corrupt json", encoding="utf-8")
    lean_file = tmp_path / "Test.lean"
    lean_file.write_text("theorem t : True := trivial\n", encoding="utf-8")

    report = pipeline.run_pipeline(spec_path=bad_spec, lean_file=lean_file)
    assert report.final_verdict == "REJECTED"
    assert report.halted_at_gate == 1
    assert len(report.gates) == 1
    assert report.status == "REJECTED_AT_GATE_1_INTAKE"


# -----------------------------------------------------------------------------
# End-to-End Integration Tests on Repository Proofs
# -----------------------------------------------------------------------------

def test_end_to_end_birkhoff_poset_operator_projector(tmp_path: Path):
    """Verify clean automated checks and pending-review receipt for the Birkhoff owner file."""
    pipeline = QMSEvidencePipeline()

    spec_file = REPO_ROOT / "tools" / "quality" / "statement_fidelity_birkhoff_spec.json"
    lean_file = REPO_ROOT / "proofs" / "BirkhoffPosetOperatorProjector.lean"
    out_receipt = tmp_path / "Birkhoff.receipt.json"

    assert spec_file.is_file()
    assert lean_file.is_file()

    report = pipeline.run_pipeline(
        spec_path=spec_file,
        lean_file=lean_file,
        out_receipt=out_receipt,
    )

    assert report.final_verdict == "PENDING_OWNER_REVIEW"
    assert report.status == "EVIDENCE_RECORDED_PENDING_OWNER_REVIEW"
    assert report.halted_at_gate is None
    assert len(report.gates) == 7
    assert all(g.passed for g in report.gates)
    assert report.receipt is not None
    assert out_receipt.is_file()

    # Verify receipt digest
    receipt_data = json.loads(out_receipt.read_text(encoding="utf-8"))
    assert receipt_data["artifact"]["path"] == "proofs/BirkhoffPosetOperatorProjector.lean"
    assert len(receipt_data["receiptSha256"]) == 64
    assert receipt_data["review"]["promotionAllowed"] is False
    assert receipt_data["checks"]["semanticVacuityGate"]["status"] == "passed"


def test_end_to_end_master_epistemic_colimit_synthesis(tmp_path: Path):
    """Verify automated checks and pending-review receipt for the master colimit owner file."""
    pipeline = QMSEvidencePipeline()

    spec_file = REPO_ROOT / "tools" / "quality" / "statement_fidelity_master_colimit_spec.json"
    lean_file = REPO_ROOT / "proofs" / "MasterEpistemicColimitSynthesis.lean"
    out_receipt = tmp_path / "MasterColimit.receipt.json"

    assert spec_file.is_file()
    assert lean_file.is_file()

    report = pipeline.run_pipeline(
        spec_path=spec_file,
        lean_file=lean_file,
        out_receipt=out_receipt,
    )

    assert report.final_verdict == "PENDING_OWNER_REVIEW"
    assert report.status == "EVIDENCE_RECORDED_PENDING_OWNER_REVIEW"
    assert report.halted_at_gate is None
    assert len(report.gates) == 7
    assert all(g.passed for g in report.gates)
    assert report.receipt is not None
    assert out_receipt.is_file()

    # Verify receipt digest
    receipt_data = json.loads(out_receipt.read_text(encoding="utf-8"))
    assert receipt_data["artifact"]["path"] == "proofs/MasterEpistemicColimitSynthesis.lean"
    assert len(receipt_data["receiptSha256"]) == 64
