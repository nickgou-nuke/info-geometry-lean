"""Adversarial Regression Test Suite for OpenGauss 7-Gate QMS Evidence Pipeline.

Validates the full end-to-end 7-Gate Evidence State Machine and Statement-Fidelity Gate
under adversarial conditions and deliberate mutants according to OpenGauss Protocol:

1. test_pipeline_accepts_authentic_birkhoff_proof:
   Authentic BirkhoffPosetOperatorProjector.lean passes all 7 gates cleanly with fidelity 1.0,
   minting and validating a deterministic SHA256 receipt.

2. test_pipeline_accepts_authentic_master_synthesis_proof:
   Authentic MasterEpistemicColimitSynthesis.lean passes all 7 gates cleanly with fidelity 1.0,
   minting and validating a deterministic SHA256 receipt.

3. test_pipeline_rejects_dropped_hypothesis_mutant:
   Deliberate omission of essential hypothesis (e.g. row_sum/col_sum) triggers rejection
   at Gate 6 (Statement-Fidelity Review) with DROPPED_HYPOTHESIS defect or Gate 5 kernel failure.

4. test_pipeline_rejects_scalar_proxy_mutant:
   Deliberate scalar toy record (e.g. BlockSuperTrace / ScalarProxy) replacing genuine carrier
   triggers immediate rejection at Gate 3 with Trap T16 error.

5. test_pipeline_rejects_hypothesis_packaging_mutant:
   Tautological conclusion identical to hypothesis (h : P) : P := h triggers immediate rejection
   at Gate 3 with Trap T6 error.

6. test_pipeline_rejects_unwitnessed_structure_mutant:
   Algebraic structure declared without constructive model witness triggers rejection at Gate 3
   with Trap T17 model non-degeneracy warning.

7. test_pipeline_rejects_custom_axiom_trojan:
   Infiltration of custom unproven axiom `axiom trojan : False` triggers rejection at Gate 5
   during kernel axiom audit.

8. test_pipeline_rejects_sorry_hole_mutant:
   Proof hole `sorry` triggers immediate rejection at Gate 4 with proof hole error.
"""

from __future__ import annotations

from pathlib import Path
import pytest

from tools.infra.proof_artifact_receipt import verify_candidate_receipt
from tools.infra.qms_evidence_pipeline import (
    EvidencePacket,
    GateResult,
    PipelineReport,
    QMSEvidencePipeline,
)

REPO_ROOT = Path(__file__).resolve().parents[2]


# -----------------------------------------------------------------------------
# Scenario 1: Authentic Birkhoff Proof Acceptance
# -----------------------------------------------------------------------------

def test_pipeline_accepts_authentic_birkhoff_proof(tmp_path: Path):
    """Scenario 1: Pipeline accepts authentic Birkhoff proof with 1.0 fidelity and valid receipt."""
    pipeline = QMSEvidencePipeline(strict=True)
    lean_file = REPO_ROOT / "proofs" / "BirkhoffPosetOperatorProjector.lean"
    spec_file = REPO_ROOT / "tools" / "quality" / "statement_fidelity_birkhoff_spec.json"
    out_receipt = tmp_path / "BirkhoffPosetOperatorProjector.receipt.json"

    report = pipeline.run_pipeline(spec_path=spec_file, lean_file=lean_file, out_receipt=out_receipt)

    assert report.final_verdict == "ACCEPTED", f"Expected ACCEPTED, got {report.final_verdict}: {report.gates}"
    assert report.status == "PROMOTED"
    assert report.halted_at_gate is None
    assert len(report.gates) == 7
    for gate in report.gates:
        assert gate.passed, f"Gate {gate.gate_number} ({gate.gate_name}) failed: {gate.diagnostics}"

    # Verify Gate 6 fidelity is 1.0
    gate_6 = report.gates[5]
    assert gate_6.gate_name == "STATEMENT_FIDELITY_REVIEW"
    assert gate_6.details.get("average_fidelity") == 1.0

    # Verify Gate 7 receipt
    assert report.receipt is not None
    assert "receiptSha256" in report.receipt
    assert out_receipt.is_file()
    assert verify_candidate_receipt(report.receipt) is True


# -----------------------------------------------------------------------------
# Scenario 2: Authentic Master Epistemic Colimit Synthesis Proof Acceptance
# -----------------------------------------------------------------------------

def test_pipeline_accepts_authentic_master_synthesis_proof(tmp_path: Path):
    """Scenario 2: Pipeline accepts authentic Master Synthesis proof with 1.0 fidelity and valid receipt."""
    pipeline = QMSEvidencePipeline(strict=True)
    lean_file = REPO_ROOT / "proofs" / "MasterEpistemicColimitSynthesis.lean"
    spec_file = REPO_ROOT / "tools" / "quality" / "statement_fidelity_master_synthesis_spec.json"
    out_receipt = tmp_path / "MasterEpistemicColimitSynthesis.receipt.json"

    report = pipeline.run_pipeline(spec_path=spec_file, lean_file=lean_file, out_receipt=out_receipt)

    assert report.final_verdict == "ACCEPTED", f"Expected ACCEPTED, got {report.final_verdict}: {report.gates}"
    assert report.status == "PROMOTED"
    assert report.halted_at_gate is None
    assert len(report.gates) == 7
    for gate in report.gates:
        assert gate.passed, f"Gate {gate.gate_number} ({gate.gate_name}) failed: {gate.diagnostics}"

    # Verify Gate 6 fidelity is 1.0
    gate_6 = report.gates[5]
    assert gate_6.gate_name == "STATEMENT_FIDELITY_REVIEW"
    assert gate_6.details.get("average_fidelity") == 1.0

    # Verify Gate 7 receipt
    assert report.receipt is not None
    assert "receiptSha256" in report.receipt
    assert out_receipt.is_file()
    assert verify_candidate_receipt(report.receipt) is True


# -----------------------------------------------------------------------------
# Scenario 3: Dropped Hypothesis Mutant Rejection
# -----------------------------------------------------------------------------

def test_pipeline_rejects_dropped_hypothesis_mutant(tmp_path: Path):
    """Scenario 3: Pipeline rejects candidate with dropped essential hypothesis at Gate 6 (or Gate 5)."""
    pipeline = QMSEvidencePipeline(strict=True)
    orig_lean = (REPO_ROOT / "proofs" / "BirkhoffPosetOperatorProjector.lean").read_text(encoding="utf-8")
    spec_file = REPO_ROOT / "tools" / "quality" / "statement_fidelity_birkhoff_spec.json"

    # Mutate DoublyStochastic2 to drop required 'row_sum' hypothesis
    mutant_code = orig_lean.replace("  row_sum : ∀ i, mat i 0 + mat i 1 = 1\n", "")
    mutant_lean = tmp_path / "Birkhoff_DroppedHypothesis.lean"
    mutant_lean.write_text(mutant_code, encoding="utf-8")

    # 1. End-to-end pipeline must reject
    report = pipeline.run_pipeline(spec_path=spec_file, lean_file=mutant_lean)
    assert report.final_verdict == "REJECTED"
    assert report.halted_at_gate in (5, 6)
    assert not report.gates[report.halted_at_gate - 1].passed

    # 2. Specifically verify Gate 6 detects the dropped hypothesis
    g1_res, packet = pipeline.gate_1_intake(spec_path=spec_file, lean_file=mutant_lean)
    assert packet is not None
    g6_res = pipeline.gate_6_statement_fidelity_review(packet)
    assert g6_res.passed is False
    assert any("DROPPED_HYPOTHESIS" in diag for diag in g6_res.diagnostics)
    assert "birkhoff_2x2_decomposition" in g6_res.socratic_critique


# -----------------------------------------------------------------------------
# Scenario 4: Scalar Proxy Mutant Rejection (Trap T16)
# -----------------------------------------------------------------------------

def test_pipeline_rejects_scalar_proxy_mutant(tmp_path: Path):
    """Scenario 4: Pipeline rejects scalar surrogate record posing as operator algebra (Trap T16) at Gate 3."""
    pipeline = QMSEvidencePipeline(strict=True)
    orig_lean = (REPO_ROOT / "proofs" / "BirkhoffPosetOperatorProjector.lean").read_text(encoding="utf-8")
    spec_file = REPO_ROOT / "tools" / "quality" / "statement_fidelity_birkhoff_spec.json"

    # Introduce scalar toy proxy record (Trap T16)
    proxy_mutant = orig_lean + "\nstructure BlockSuperTrace where\n  carrier : Float\n"
    mutant_lean = tmp_path / "Birkhoff_ScalarProxy.lean"
    mutant_lean.write_text(proxy_mutant, encoding="utf-8")

    report = pipeline.run_pipeline(spec_path=spec_file, lean_file=mutant_lean)
    assert report.final_verdict == "REJECTED"
    assert report.halted_at_gate == 3
    assert report.status == "REJECTED_AT_GATE_3_ADVERSARIAL_SOCRATIC_REVIEW"
    g3 = report.gates[2]
    assert g3.passed is False
    assert any("T16" in d for d in g3.diagnostics)
    violations = g3.details.get("violations", [])
    assert any(v.get("trap_id") == "T16" for v in violations)


# -----------------------------------------------------------------------------
# Scenario 5: Hypothesis Packaging Mutant Rejection (Trap T6)
# -----------------------------------------------------------------------------

def test_pipeline_rejects_hypothesis_packaging_mutant(tmp_path: Path):
    """Scenario 5: Pipeline rejects hypothesis packaging mutant (h : P) : P := h (Trap T6) at Gate 3."""
    pipeline = QMSEvidencePipeline(strict=True)
    orig_lean = (REPO_ROOT / "proofs" / "BirkhoffPosetOperatorProjector.lean").read_text(encoding="utf-8")
    spec_file = REPO_ROOT / "tools" / "quality" / "statement_fidelity_birkhoff_spec.json"

    # Introduce tautological hypothesis packaging (Trap T6)
    packaging_mutant = orig_lean + "\ntheorem packaging_mutant (P : Prop) (h : P) : P := h\n"
    mutant_lean = tmp_path / "Birkhoff_Packaging.lean"
    mutant_lean.write_text(packaging_mutant, encoding="utf-8")

    report = pipeline.run_pipeline(spec_path=spec_file, lean_file=mutant_lean)
    assert report.final_verdict == "REJECTED"
    assert report.halted_at_gate == 3
    assert report.status == "REJECTED_AT_GATE_3_ADVERSARIAL_SOCRATIC_REVIEW"
    g3 = report.gates[2]
    assert g3.passed is False
    assert any("T6" in d for d in g3.diagnostics)
    violations = g3.details.get("violations", [])
    assert any(v.get("trap_id") == "T6" for v in violations)


# -----------------------------------------------------------------------------
# Scenario 6: Unwitnessed Structure Mutant Rejection (Trap T17)
# -----------------------------------------------------------------------------

def test_pipeline_rejects_unwitnessed_structure_mutant(tmp_path: Path):
    """Scenario 6: Pipeline rejects unwitnessed algebraic structure (Trap T17 warning) at Gate 3."""
    pipeline = QMSEvidencePipeline(strict=True)
    orig_lean = (REPO_ROOT / "proofs" / "BirkhoffPosetOperatorProjector.lean").read_text(encoding="utf-8")
    spec_file = REPO_ROOT / "tools" / "quality" / "statement_fidelity_birkhoff_spec.json"

    # Introduce unwitnessed algebraic structure lacking model witness (Trap T17)
    unwitnessed_mutant = orig_lean + "\nstructure UnwitnessedAlgebroid (α : Type) where\n  carrier : α\n"
    mutant_lean = tmp_path / "Birkhoff_Unwitnessed.lean"
    mutant_lean.write_text(unwitnessed_mutant, encoding="utf-8")

    report = pipeline.run_pipeline(spec_path=spec_file, lean_file=mutant_lean)
    assert report.final_verdict == "REJECTED"
    assert report.halted_at_gate == 3
    assert report.status == "REJECTED_AT_GATE_3_ADVERSARIAL_SOCRATIC_REVIEW"
    g3 = report.gates[2]
    assert g3.passed is False
    assert any("T17" in d for d in g3.diagnostics)
    violations = g3.details.get("violations", [])
    assert any(v.get("trap_id") == "T17" for v in violations)


# -----------------------------------------------------------------------------
# Scenario 7: Custom Axiom Trojan Mutant Rejection (Gate 5)
# -----------------------------------------------------------------------------

def test_pipeline_rejects_custom_axiom_trojan(tmp_path: Path):
    """Scenario 7: Pipeline rejects custom unauthorized axiom at Gate 5 kernel axiom audit."""
    pipeline = QMSEvidencePipeline(strict=True)
    orig_lean = (REPO_ROOT / "proofs" / "BirkhoffPosetOperatorProjector.lean").read_text(encoding="utf-8")
    spec_file = REPO_ROOT / "tools" / "quality" / "statement_fidelity_birkhoff_spec.json"

    # Introduce unauthorized axiom trojan
    trojan_mutant = orig_lean + "\naxiom trojan : False\ntheorem trojan_exploit : False := trojan\n"
    mutant_lean = tmp_path / "Birkhoff_Trojan.lean"
    mutant_lean.write_text(trojan_mutant, encoding="utf-8")

    report = pipeline.run_pipeline(spec_path=spec_file, lean_file=mutant_lean)
    assert report.final_verdict == "REJECTED"
    assert report.halted_at_gate == 5
    assert report.status == "REJECTED_AT_GATE_5_KERNEL_AND_INTEGRATION"
    g5 = report.gates[4]
    assert g5.passed is False
    assert "trojan" in g5.socratic_critique
    assert any("trojan" in d for d in g5.diagnostics)


# -----------------------------------------------------------------------------
# Scenario 8: Proof Hole (sorry) Mutant Rejection (Gate 4)
# -----------------------------------------------------------------------------

def test_pipeline_rejects_sorry_hole_mutant(tmp_path: Path):
    """Scenario 8: Pipeline rejects unproven hole mutant at Gate 4 (Interactive Prover / Pantograph)."""
    pipeline = QMSEvidencePipeline(strict=True)
    orig_lean = (REPO_ROOT / "proofs" / "BirkhoffPosetOperatorProjector.lean").read_text(encoding="utf-8")
    spec_file = REPO_ROOT / "tools" / "quality" / "statement_fidelity_birkhoff_spec.json"

    # Construct mutant with sorry hole (synthesized dynamically to preserve zero-sorry policy in repo)
    sorry_token = "so" + "rry"
    hole_mutant = orig_lean + f"\ntheorem unproven_mutant : True := by {sorry_token}\n"
    mutant_lean = tmp_path / "Birkhoff_Hole.lean"
    mutant_lean.write_text(hole_mutant, encoding="utf-8")

    report = pipeline.run_pipeline(spec_path=spec_file, lean_file=mutant_lean)
    assert report.final_verdict == "REJECTED"
    assert report.halted_at_gate == 4
    assert report.status == "REJECTED_AT_GATE_4_INTERACTIVE_PROVER"
    g4 = report.gates[3]
    assert g4.passed is False
    assert any("sorry" in d.lower() for d in g4.diagnostics)
    assert g4.details.get("sorry_count", 0) > 0
