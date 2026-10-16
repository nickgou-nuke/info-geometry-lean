"""Comprehensive Test Suite for OpenGauss / TeamAntigravity Unified CLI.

Verifies all 15 OpenGauss commands natively:
1.  /prove        - Top-Down Assume-and-Recurse Prover
2.  /check        - Ground-Truthed Counterexample Hunter & Consistency Auditor
3.  /refute       - Adversarial False-as-Stated Screener (15-Trap Catalog)
4.  /draft        - Skeleton Drafter
5.  /review       - Automated QMS Source Preflight (Gate 2 / Gate 4)
6.  /checkpoint   - State Saver & Continuous Tracker
7.  /refactor     - Proof Refactorer & Redundancy Cleaner
8.  /golf         - Proof Optimizer
9.  /autoprove    - Autonomous Multi-Cycle Engine (M10 Re-Hydration)
10. /formalize    - Two-Phase Interactive Synthesis Assistant
11. /autoformalize - End-to-End CAS to Lean 4 Invariant Translator
12. /handoff      - Cross-Session Context Preserver
13. /discover     - Mathematical Declaration & Carrier Hunter
14. /quarantine   - Rejected Route & Residue Obstruction Isolator
15. /certify      - Companion Axiom Certification Script Generator
"""

from __future__ import annotations

import json
import io
from contextlib import redirect_stdout
from pathlib import Path
from types import SimpleNamespace
from typing import Optional
from unittest.mock import patch

from tools.infra.opengauss_cli import (
    analyze_golf_opportunities,
    analyze_refactor_candidates,
    autoformalize_cas_identity,
    check_consistency,
    discover_declarations,
    draft_skeleton,
    execute_checkpoint,
    generate_certification_audit,
    generate_handoff_context,
    main,
    plan_top_down_proof,
    quarantine_obstruction,
    refute_content,
    review_file,
    run_autoprove_cycle,
    run_formalize,
)


def test_command_1_prove():
    """Verify /prove top-down decomposition and Anti-T11 enforcement."""
    sublemmas = [
        {"name": "h_comm", "type": "a * b = b * a"},
        {"name": "h_assoc", "type": "a * (b * c) = (a * b) * c"},
    ]
    decomp = plan_top_down_proof(
        headline="ring_unification",
        headline_type="∀ a b c : R, a * b * c = c * b * a",
        sublemmas=sublemmas,
        glue_tactic="exact h_comm h_assoc",
    )
    assert decomp.headline == "ring_unification"
    assert len(decomp.sublemmas) == 2
    assert decomp.status == "PLAN_COMPILED"
    assert decomp.anti_t11_compliant is True
    assert any("ring_unification" in step for step in decomp.plan)


def test_command_2_check():
    """Verify /check consistency checks and counterexample detection."""
    # Contradictory hypothesis should trigger high risk
    res_bad = check_consistency(
        expression="x > 0",
        hypotheses=["0 = 1", "x > 0"],
    )
    assert not res_bad.consistent
    assert res_bad.counterexample_risk == "HIGH"

    # Krein space positive-definite signature clash (Trap T13)
    res_krein = check_consistency(
        expression="KreinSpace V ∧ PositiveDefinite (inner : V → V → ℝ)",
    )
    assert not res_krein.consistent
    assert res_krein.counterexample_risk == "HIGH"
    assert any("Trap T13" in w for w in res_krein.warnings)

    # Clean statement
    res_clean = check_consistency(
        expression="a + b = b + a",
        hypotheses=["a : ℝ", "b : ℝ"],
    )
    assert res_clean.consistent
    assert res_clean.counterexample_risk == "NONE"


def test_command_3_refute():
    """Verify /refute catches trap violations (T1, T3, T4, T6, T16)."""
    bad_code = """
    theorem packaged (P : Prop) (h : P) : P := by
      exact h

    theorem bad_flat (M : Type*) [HasLocallyConstantChartAt M] : True := by
      trivial

    structure BlockSuperTrace (R : Type*) where
      tr_A : R
      tr_D : R
    """
    res = refute_content(bad_code, filename="test_bad.lean")
    assert not res["clean"]
    assert res["total_traps"] >= 3
    assert res["verdict"] == "REJECT"
    trap_ids = [e["trap_id"] for e in res["errors"]]
    assert "T6" in trap_ids
    assert "T3" in trap_ids
    assert "T16" in trap_ids


def test_refute_missing_path_fails():
    assert main(["refute", "this-path-does-not-exist.lean", "--json"]) == 1



def test_command_4_draft(tmp_path: Optional[Path] = None):
    """Verify /draft generates valid Lean 4 declaration skeleton with leaves and glue."""
    if tmp_path is None:
        import tempfile
        tmp_path = Path(tempfile.mkdtemp())
    sublemmas = [
        {"name": "step1_kernel", "type": "LinearMap.ker T = 0", "doc": "Injectivity of T."},
        {"name": "step2_range", "type": "LinearMap.range T = ⊤", "doc": "Surjectivity of T."},
    ]
    code = draft_skeleton(
        headline="operator_bijective",
        signature="(T : E →ₗ[ℝ] E) : Function.Bijective T",
        sublemmas=sublemmas,
        namespace="InfoGeometry.TestDraft",
        docstring="Grand unification isomorphism.",
    )
    assert "namespace InfoGeometry.TestDraft" in code
    assert "lemma step1_kernel" in code
    assert "lemma step2_range" in code
    assert "theorem operator_bijective" in code
    assert "exact step1_kernel step2_range" in code
    assert "end InfoGeometry.TestDraft" in code


def test_command_5_review(tmp_path: Optional[Path] = None):
    """Verify /review audit under QMS-SOP-IAA-001 (Gate 2 & Gate 4)."""
    if tmp_path is None:
        import tempfile
        tmp_path = Path(tempfile.mkdtemp())
    clean_file = tmp_path / "Clean.lean"
    clean_file.write_text(
        "import Mathlib.Tactic\n\n"
        "theorem add_comm_test (x y : ℝ) : x + y = y + x := by ring\n",
        encoding="utf-8",
    )
    rep2 = review_file(clean_file, gate="GATE_2")
    assert rep2.verdict == "PASS"
    assert rep2.sorry_count == 0
    assert rep2.review_authority == "automated_source_preflight"
    assert rep2.independent_semantic_audit_performed is False

    rep4 = review_file(clean_file, gate="GATE_4")
    assert rep4.verdict == "STATIC_REVIEW_PASSED_KERNEL_UNVERIFIED"
    assert rep4.kernel_checked is False
    assert rep4.custom_axioms is None
    assert rep4.review_authority == "automated_source_preflight"
    assert rep4.independent_semantic_audit_performed is False

    # Static screening rejects repo-authored axiom declarations immediately via QMS_AXIOM.
    unverified_file = tmp_path / "Unverified.lean"
    unverified_file.write_text(
        "axiom made_up : False\ntheorem false_claim : False := made_up\n",
        encoding="utf-8",
    )
    rep_unverified = review_file(unverified_file, gate="GATE_4")
    assert rep_unverified.verdict == "REJECTED"
    assert any(t["trap_id"] == "QMS_AXIOM" for t in rep_unverified.trap_violations)
    assert rep_unverified.kernel_checked is False
    assert rep_unverified.custom_axioms is None

    # Test file with sorry and hype
    dirty_file = tmp_path / "Dirty.lean"
    dirty_file.write_text(
        "-- This file proves quantum gravity completely!\n"
        "theorem dirty_unification : True := by sorry\n",
        encoding="utf-8",
    )
    rep_dirty = review_file(dirty_file, gate="GATE_4")
    assert rep_dirty.verdict == "REJECTED"
    assert rep_dirty.sorry_count == 1
    assert len(rep_dirty.scope_inflation_warnings) >= 1


def test_review_json_distinguishes_automated_preflight_from_independent_audit(tmp_path: Optional[Path] = None):
    if tmp_path is None:
        import tempfile
        tmp_path = Path(tempfile.mkdtemp())
    source = tmp_path / "ReviewAuthority.lean"
    source.write_text("theorem review_authority_test : True := by trivial\n", encoding="utf-8")
    output = io.StringIO()
    # Isolate this output-contract test from the caller's staged index. The
    # staged hook has its own integration coverage.
    with patch(
        "tools.infra.opengauss_cli.subprocess.run",
        return_value=SimpleNamespace(returncode=0, stderr="", stdout=""),
    ), redirect_stdout(output):
        assert main(["review", str(source), "--gate", "GATE_2", "--json"]) == 0
    report = json.loads(output.getvalue())[0]
    assert report["review_authority"] == "automated_source_preflight"
    assert report["independent_semantic_audit_performed"] is False


def test_command_6_checkpoint():
    """Verify checkpoint captures state without staging unrelated work."""
    receipt = execute_checkpoint(message="Unit test checkpoint verification", dry_run=False)
    assert receipt.status == "CHECKPOINT_SAVED"
    assert receipt.git_head != ""
    assert isinstance(receipt.staged_files, list)


def test_command_7_refactor():
    """Verify /refactor identifies monolithic proof blocks >25 lines."""
    monolithic_code = """
    theorem monolithic_proof (x : ℝ) : x = x := by
""" + "\n".join(f"      have h{i} : x = x := by rfl" for i in range(30)) + """
      rfl
    theorem next_decl : True := trivial
    """
    suggestions = analyze_refactor_candidates(monolithic_code)
    assert len(suggestions) >= 1
    assert suggestions[0].target_block == "monolithic_proof"
    assert "violates the Lean File Size & Lemma Reuse Mandate" in suggestions[0].rationale


def test_command_8_golf():
    """Verify /golf detects redundant tactic patterns."""
    golfable_code = """
    theorem golf_me (a b : ℝ) : (a + b)^2 = a^2 + 2*a*b + b^2 := by
      simp only [add_sq]; ring

    theorem id_prop (x : ℝ) : x = x := by exact rfl
    """
    golfs = analyze_golf_opportunities(golfable_code)
    assert len(golfs) >= 2
    replacements = [g.suggested_replacement for g in golfs]
    assert "ring" in replacements
    assert ":= rfl" in replacements


def test_command_9_autoprove(tmp_path: Optional[Path] = None):
    """Verify /autoprove multi-cycle state management, M10 Re-Hydration, and Pillar II quarantine ingestion."""
    if tmp_path is None:
        import tempfile
        tmp_path = Path(tempfile.mkdtemp())
    target = tmp_path / "Target.lean"
    target.write_text(
        "-- comment mentioning sorry should be ignored\n"
        "theorem step1 : True := trivial\n"
        "theorem step2 : True := by sorry\n",
        encoding="utf-8",
    )
    state = run_autoprove_cycle(str(target), cycle=1, max_cycles=3, repo_root=tmp_path)
    assert state.open_sorries == 1
    assert state.status == "INSPECTION_ONLY"
    assert state.proof_attempted is False
    assert state.proven_lemmas == []
    assert len(state.dead_routes) >= 1
    assert "Trap T15" in state.dead_routes[0]

    # Quarantine an obstruction for Target.lean and verify autoprove ingests its negative_constraint
    quarantine_obstruction(
        file=str(target),
        trap_id="T16",
        description="Scalar surrogate used in place of matrix carrier",
        counterexample="Mat2 R noncommutativity fails over scalar proxy",
        negative_constraint="DO NOT use scalar trace proxy for Target.lean",
        repo_root=tmp_path,
    )
    state_with_quarantine = run_autoprove_cycle(str(target), cycle=2, max_cycles=3, repo_root=tmp_path)
    assert "DO NOT use scalar trace proxy for Target.lean" in state_with_quarantine.dead_routes


def test_command_10_formalize():
    """Verify /formalize phase 1 alignment and phase 2 code generation."""
    spec = "Construct inductive UHF colimit boundary for Cuntz algebra."
    plan_phase1 = run_formalize(spec, phase=1)
    assert "InfoGeometry.Canonical.TensorTowerColimit" in plan_phase1.categorical_anchors
    assert "InfoGeometry.Canonical.NoncommutativeOperatorContinuumArchetypes" in plan_phase1.categorical_anchors
    assert plan_phase1.screened_clean is True

    plan_phase2 = run_formalize(spec, phase=2)
    assert plan_phase2.synthesized_lean == ""
    assert plan_phase2.synthesis_status == "NEEDS_TYPED_TARGET"


def test_command_11_autoformalize():
    """Verify /autoformalize translates CAS invariants into typed Lean 4 theorems."""
    # Test matrix det invariant
    trans_mat = autoformalize_cas_identity(
        cas_type="sympy",
        expression="sl2 matrix det = 1",
        theorem_name="sl2_det_identity",
    )
    assert "Matrix.det_fin_two" in trans_mat.lean_code
    assert trans_mat.verified is False
    assert trans_mat.verification_status == "not_run"

    # Test polynomial identity
    trans_poly = autoformalize_cas_identity(
        cas_type="sympy",
        expression="(x + y)^2 = x^2 + 2*x*y + y^2",
        theorem_name="binomial_identity",
    )
    assert "by\n  ring" in trans_poly.lean_code


def test_command_12_handoff():
    """Verify /handoff serializes structured context and anti-compaction anchors."""
    targets = ["lean/InfoGeometry/Cosmology/SpacetimeParabolicQuotient.lean"]
    checkpoints = ["GNSQuotientCosetEquivalence.lean verified with 0 sorry"]
    ctx = generate_handoff_context(
        active_targets=targets,
        verified_checkpoints=checkpoints,
    )
    assert "SpacetimeParabolicQuotient.lean" in ctx.handoff_markdown
    assert "GNSQuotientCosetEquivalence.lean" in ctx.handoff_markdown
    assert "Trap T15" in ctx.handoff_markdown
    assert len(ctx.dead_routes) >= 2


def test_command_13_discover():
    """Verify /discover scans for matching declarations, carriers, and recommended imports."""
    report = discover_declarations("split quaternion", repo_root=Path("."))
    assert report.query == "split quaternion"
    assert len(report.carriers_found) > 0
    assert any(c["name"] == "Coquaternion" for c in report.carriers_found)
    assert len(report.lemmas_found) > 0
    assert any("planar_triad" in l["name"] for l in report.lemmas_found)
    assert isinstance(report.recommended_imports, set)
    assert "InfoGeometry.Clifford.CockleCoquaternionPlanarTriad" in report.recommended_imports
    assert len(report.deduplication_warnings) > 0
    assert any("Coquaternion" in w for w in report.deduplication_warnings)

    d = report.to_dict()
    assert isinstance(d["recommended_imports"], list)
    serialized = json.dumps(d)
    assert "CockleCoquaternionPlanarTriad" in serialized


def test_command_14_quarantine(tmp_path: Optional[Path] = None):
    """Verify /quarantine ingests rejected attempt into TypedObstructionPacket and persists it."""
    if tmp_path is None:
        import tempfile
        tmp_path = Path(tempfile.mkdtemp())

    packet = quarantine_obstruction(
        file="lean/InfoGeometry/Physics/BadTheory.lean",
        trap_id="T13",
        description="Asserted positive definiteness on indefinite Krein space",
        counterexample="Negative norm vectors exist in Krein space: inner(v, v) < 0",
        negative_constraint="DO NOT assert positive-definite inner product over Krein spaces",
        repo_root=tmp_path,
    )
    assert packet.source_file == "lean/InfoGeometry/Physics/BadTheory.lean"
    assert packet.trap_id == "T13"
    assert packet.packet_id.startswith("obs_")
    assert "Krein" in packet.negative_constraint

    quarantine_file = tmp_path / "artifacts" / "residue_quarantine" / f"{packet.packet_id}.json"
    assert quarantine_file.is_file()
    data = json.loads(quarantine_file.read_text(encoding="utf-8"))
    assert data["packet_id"] == packet.packet_id
    assert data["trap_id"] == "T13"
    assert data["description"] == packet.description
    assert data["counterexample"] == packet.counterexample
    assert data["negative_constraint"] == packet.negative_constraint


def test_command_15_certify(tmp_path: Optional[Path] = None):
    """Verify /certify extracts all theorems and emits companion #print axioms script."""
    if tmp_path is None:
        import tempfile
        tmp_path = Path(tempfile.mkdtemp())

    mock_lean = tmp_path / "TestModule.lean"
    mock_lean.write_text(
        "-- theorem commented_out : False := by sorry\n"
        "/- namespace AlsoFake -/\n"
        "namespace InfoGeometry.Test\n\n"
        "theorem alpha_eq : 1 = 1 := rfl\n"
        "private theorem hidden_eq : 1 = 1 := rfl\n"
        "private\n"
        "theorem hidden_multiline_eq : 1 = 1 := rfl\n"
        "lemma beta_pos (n : Nat) : n + 0 = n := Nat.add_zero n\n"
        "end InfoGeometry.Test\n"
        "namespace Other\ntheorem gamma_eq : 2 = 2 := rfl\nend Other\n"
        "namespace InfoGeometry.Test\ntheorem reopened_eq : 3 = 3 := rfl\nend InfoGeometry.Test\n"
        "namespace Dotted.Scope\ntheorem dotted_eq : 4 = 4 := rfl\nend Dotted.Scope\n"
        "namespace Outer\nsection Outer\n"
        "theorem scoped_eq : 5 = 5 := rfl\nend Outer\n"
        "theorem after_section_eq : 6 = 6 := rfl\nend Outer\n",
        encoding="utf-8",
    )

    audit = generate_certification_audit(mock_lean, write_audit=True, repo_root=tmp_path)
    assert audit.source_file == str(mock_lean)
    assert audit.audit_file == str(tmp_path / "TestModuleAudit.lean")
    assert audit.theorems == [
        "InfoGeometry.Test.alpha_eq",
        "InfoGeometry.Test.beta_pos",
        "Other.gamma_eq",
        "InfoGeometry.Test.reopened_eq",
        "Dotted.Scope.dotted_eq",
        "Outer.scoped_eq",
        "Outer.after_section_eq",
    ]
    assert audit.written is True
    assert audit.audit_script.startswith(
        "/-\n"
        "Copyright (c) 2026 InfoGeometry Authors. All rights reserved.\n"
        "Released under Apache 2.0 license as described in the file LICENSE.\n"
        "Authors: InfoGeometry Engine Contributors\n"
        "-/\n\n"
    )
    assert "import TestModule" in audit.audit_script
    assert "#print axioms InfoGeometry.Test.alpha_eq" in audit.audit_script
    assert "#print axioms InfoGeometry.Test.beta_pos" in audit.audit_script
    assert "#print axioms Other.gamma_eq" in audit.audit_script
    assert "#print axioms InfoGeometry.Test.reopened_eq" in audit.audit_script
    assert "#print axioms Dotted.Scope.dotted_eq" in audit.audit_script
    assert "#print axioms Outer.scoped_eq" in audit.audit_script
    assert "#print axioms Outer.after_section_eq" in audit.audit_script
    assert "commented_out" not in audit.audit_script
    assert "hidden_eq" not in audit.audit_script
    assert "hidden_multiline_eq" not in audit.audit_script
    assert Path(audit.audit_file).is_file()
    assert Path(audit.audit_file).read_text(encoding="utf-8") == audit.audit_script

    cockle_file = Path("lean/InfoGeometry/Clifford/CockleCoquaternionPlanarTriad.lean")
    if cockle_file.is_file():
        audit_cockle = generate_certification_audit(cockle_file, write_audit=False)
        assert len(audit_cockle.theorems) >= 10
        assert "InfoGeometry.Clifford.Coquaternion.Coquaternion.planar_triad_coexistence" in audit_cockle.theorems
        assert "#print axioms InfoGeometry.Clifford.Coquaternion.Coquaternion.planar_triad_coexistence" in audit_cockle.audit_script
        assert audit_cockle.written is False


def test_cli_dispatch_main(capsys=None):
    """Verify all 15 commands dispatch cleanly through main()."""
    # 1. prove
    rc = main(["prove", "--headline", "test_thm", "--type", "True", "--json"])
    assert rc == 0

    # 2. check
    rc = main(["check", "--expr", "x = x", "--json"])
    assert rc == 0

    # 3. refute
    rc = main(["refute", "lean/InfoGeometry/Clifford/CockleCoquaternionPlanarTriad.lean", "--json"])
    assert rc == 0

    # 4. draft
    rc = main(["draft", "--headline", "t_draft", "--signature", ": True", "--scratch", "--json"])
    assert rc == 0
    # 5. review
    rc = main(["review", "proofs/WavefrontKMSKleinDuality.lean", "--gate", "GATE_2", "--json"])
    assert rc == 0

    # 6. checkpoint
    rc = main(["checkpoint", "--dry-run", "--json"])
    assert rc == 0

    # 7. refactor
    rc = main(["refactor", "lean/InfoGeometry/Clifford/CockleCoquaternionPlanarTriad.lean", "--json"])
    assert rc == 0

    # 8. golf
    rc = main(["golf", "lean/InfoGeometry/Clifford/CockleCoquaternionPlanarTriad.lean", "--json"])
    assert rc == 0

    # 9. autoprove
    rc = main(["autoprove", "lean/InfoGeometry/Clifford/CockleCoquaternionPlanarTriad.lean", "--cycles", "1", "--json"])
    assert rc == 0

    # 10. formalize
    rc = main(["formalize", "--spec", "UHF colimit", "--phase", "1", "--json"])
    assert rc == 0

    # 11. autoformalize
    rc = main(["autoformalize", "--cas", "sympy", "--expr", "a + b = b + a", "--json"])
    assert rc == 0

    # 12. handoff
    rc = main(["handoff", "--targets", "test.lean", "--json"])
    assert rc == 0

    # 13. discover
    rc = main(["discover", "--query", "split quaternion", "--json"])
    assert rc == 0

    # 14. quarantine
    import tempfile
    quarantine_root = Path(tempfile.mkdtemp())
    rc = main([
        "quarantine",
        "--file", "lean/InfoGeometry/Bad.lean",
        "--trap", "T4",
        "--desc", "Vacuous hypothesis",
        "--counter", "Trivial 0 = 0",
        "--constraint", "DO NOT use vacuous binders",
        "--repo-root", str(quarantine_root),
        "--json",
    ])
    assert rc == 0

    # 15. certify
    rc = main(["certify", "--file", "lean/InfoGeometry/Clifford/CockleCoquaternionPlanarTriad.lean", "--json"])
    assert rc == 0


def test_scratch_draft_cannot_write_a_source_file():
    try:
        main([
            "draft", "--headline", "t_draft", "--signature", ": True",
            "--scratch", "--output", "scratch/UnboundDraft.lean",
        ])
    except SystemExit:
        return
    raise AssertionError("scratch draft unexpectedly accepted a source output path")


if __name__ == "__main__":
    import inspect
    import sys
    current_module = sys.modules[__name__]
    passed = 0
    failed = 0
    for name, obj in inspect.getmembers(current_module):
        if name.startswith("test_") and inspect.isfunction(obj):
            try:
                obj()
                passed += 1
                print(f"✓ {name}")
            except Exception as e:
                failed += 1
                print(f"✗ {name}: {e}")
    print(f"\nRan {passed + failed} tests: {passed} passed, {failed} failed.")
    sys.exit(0 if failed == 0 else 1)
