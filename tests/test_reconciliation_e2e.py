"""Pytest entrypoint for the 218-check R1/R2/R3 Reconciliation E2E Suite (Tiers 1-4)."""

from __future__ import annotations

from collections import Counter
import os
from pathlib import Path

import pytest

from tests.reconciliation_e2e import REPO_ROOT, get_mode
from tests.reconciliation_e2e.lean_probes import (
    _parse_declarations,
    parse_declarations_from_text,
    run_milestone_contract_probe,
)
from tests.reconciliation_e2e.manifest import (
    CHECKS,
    F2_5_BASELINE_ALL,
    CheckSpec,
    checks_by_id,
    get_summary_counts,
    is_active_for_mode,
)
from tests.reconciliation_e2e.quality_runner import _extract_leading_json_list
from tests.reconciliation_e2e.rubric_checker import (
    detect_bucket3_overclaims_in_text,
    verify_doc_symbols,
    verify_klein_grassmann_plucker_docs,
    verify_no_bucket3_overclaims,
)
from tests.reconciliation_e2e.run_e2e import _collect_m1_m2_m3_files, execute_check


def test_manifest_counts_match_e2e_spec():
    counts = get_summary_counts()
    assert counts["tier1"] == 92
    assert counts["tier2"] == 92
    assert counts["tier3"] == 23
    assert counts["tier4"] == 11
    assert counts["total"] == 218
    ids = [c.check_id for c in CHECKS]
    assert len(ids) == len(set(ids)) == 218
    t1_feat = Counter(c.feature for c in CHECKS if c.tier == 1)
    t2_feat = Counter(c.feature for c in CHECKS if c.tier == 2)
    assert len(t1_feat) == 18 and all(v >= 5 for v in t1_feat.values())
    assert len(t2_feat) == 18 and all(v >= 5 for v in t2_feat.values())


def test_lean_probes_comment_strip_ns_stack_and_fail_closed(tmp_path: Path):
    src = """
/-! docstring mentioning `twoFormAlternatingEquiv` and `DerivationOperatorForm` -/
-- line comment: `def fakeCommentDecl`
namespace Outer.Inner
section Helper
theorem multi_line_thm
    {A : Type*} [Ring A]
    (x : A) :
    x = x := rfl
end Helper
end Outer.Inner
"""
    decls = parse_declarations_from_text(src)
    assert [d.fqn for d in decls] == ["Outer.Inner.multi_line_thm"]

    # Empty decl_names must fail closed when no probe_body is supplied
    scratch_probe = REPO_ROOT / "scratch" / "e2e_reconciliation" / "_tmp_empty_decl_unit.lean"
    scratch_probe.parent.mkdir(parents=True, exist_ok=True)
    try:
        scratch_probe.write_text("namespace Foo\nvariable (x_marker : Nat)\nend Foo\n", encoding="utf-8")
        rel = os.path.relpath(scratch_probe, REPO_ROOT)
        res = run_milestone_contract_probe(
            "UNIT-EMPTY-DECL",
            {"candidate_files": [rel], "required_patterns": [r"x_marker"], "co_occur": True},
        )
        assert not res.passed
        assert "No concrete Lean declarations extracted" in res.summary
    finally:
        scratch_probe.unlink(missing_ok=True)


def test_lean_probes_unicode_identifiers_and_decl_cap_decoupled():
    # Real owner file must parse Unicode ι declarations intact without truncation
    grace_fqns = [
        d.fqn for d in _parse_declarations("lean/InfoGeometry/Clifford/GradedGraceContraction.lean")
    ]
    assert "InfoGeometry.Clifford.GradedGraceContraction.clifford_ι_injective" in grace_fqns
    assert "InfoGeometry.Clifford.GradedGraceContraction.equivExterior_ι" in grace_fqns
    assert "InfoGeometry.Clifford.GradedGraceContraction.ι_mem_exteriorPower_one" in grace_fqns

    src = """
namespace Outer.Unicode
private
def priv_prev_line : Nat := 0
mutual
  def e₀ : Nat := 1
  def h3_diag₁ : Nat := 2
end
theorem after_mutual : True := trivial
end Outer.Unicode
"""
    decls = {d.short_name: d for d in parse_declarations_from_text(src)}
    assert decls["priv_prev_line"].is_private is True
    assert decls["e₀"].fqn == "Outer.Unicode.e₀"
    assert decls["h3_diag₁"].fqn == "Outer.Unicode.h3_diag₁"
    assert decls["after_mutual"].fqn == "Outer.Unicode.after_mutual"

    # forbidden_scope="decl" must inspect 3rd+ matching declaration (not capped at 2)
    third_decl_probe = REPO_ROOT / "scratch" / "e2e_reconciliation" / "_tmp_third_decl_unit.lean"
    third_decl_probe.parent.mkdir(parents=True, exist_ok=True)
    try:
        third_decl_probe.write_text(
            "namespace ThirdDeclTest\n"
            "def target_marker_1 : Nat := 1\n"
            "def target_marker_2 : Nat := 2\n"
            "def target_marker_3 {A : Type*} [CommRing A] : Nat := 3\n"
            "end ThirdDeclTest\n",
            encoding="utf-8",
        )
        rel = os.path.relpath(third_decl_probe, REPO_ROOT)
        res = run_milestone_contract_probe(
            "UNIT-THIRD-DECL-FORBIDDEN",
            {
                "candidate_files": [rel],
                "required_patterns": [r"target_marker_"],
                "forbidden_patterns": [r"\[CommRing\s+A\]"],
                "forbidden_scope": "decl",
                "co_occur": True,
            },
        )
        assert not res.passed
        assert "ThirdDeclTest.target_marker_3" in res.summary
    finally:
        third_decl_probe.unlink(missing_ok=True)

    # Leading diagnostic with '[' must not break _extract_leading_json_list
    parsed = _extract_leading_json_list(
        '[lock] waiting [1/2]\n[{"module": "InfoGeometry.Dummy", "passed": true}]\n'
    )
    assert parsed == [{"module": "InfoGeometry.Dummy", "passed": True}]


def test_rubric_bucket3_overclaims_and_grassmann_order(tmp_path: Path):
    assert detect_bucket3_overclaims_in_text("p.md", "BUCKET 1: internal Kasparov product is proved.")
    assert detect_bucket3_overclaims_in_text("s.md", "We prove continuum 4D Yang-Mills [BUCKET 1].")
    assert detect_bucket3_overclaims_in_text("m.md", "### BUCKET 1\n- W_{4,4} ≃ TM ⊕ T*M\n")
    assert detect_bucket3_overclaims_in_text("b.md", "**BUCKET 1:**\n- continuum 4D Yang-Mills\n")
    assert detect_bucket3_overclaims_in_text("c.md", "### BUCKET 1\n- C*-correspondence proved\n")
    assert detect_bucket3_overclaims_in_text("w.md", "BUCKET 1: 4D continuum Yang-Mills is proved.")
    assert not detect_bucket3_overclaims_in_text("h.md", "### BUCKET 3\n- continuum 4D Yang-Mills\n")

    reordered = REPO_ROOT / "scratch" / "e2e_reconciliation" / "_tmp_grassmann_unit.md"
    reordered.parent.mkdir(parents=True, exist_ok=True)
    try:
        reordered.write_text(
            "Crelle 1852; p. 278 (1862); 1844; regressive Plücker; syncyclic Möbius; Darboux Note VI\n",
            encoding="utf-8",
        )
        rel = os.path.relpath(reordered, REPO_ROOT)
        assert verify_klein_grassmann_plucker_docs([rel])["passed"]
        assert verify_no_bucket3_overclaims([rel])["passed"]
    finally:
        reordered.unlink(missing_ok=True)


def test_verify_doc_symbols_real_specs_and_fake_rejections():
    # R1 spec must pass cleanly with zero missing symbols
    r1_res = verify_doc_symbols(["docs/R1_NONCOMMUTATIVE_DIFFERENTIAL_GEOMETRY_SPEC.md"])
    assert r1_res["passed"], r1_res

    # R3 spec must have zero false positives on module stems, Mathlib names, and Lean sections
    r3_res = verify_doc_symbols(["docs/R3_CLIFFORD_TOWERS_AND_INVARIANCE_SPEC.md"])
    r3_missing_str = "\n".join(r3_res["missing_symbols"])
    for non_false_pos in (
        "DirectLimit",
        "DirectedSystem",
        "DiscreteTopology",
        "IsometryEquiv",
        "equivExterior",
        "evenOdd",
        "equivOfIsometry",
        "HasDerivAt",
        "GeneralRing",
        "InvertibleTwo",
        "RealGraceInvariance",
        "non_theorem_claims",
        "splitCliffordLift_evenOdd",
        "GradedGraceContraction",
        "SplitCliffordTowerUnification",
    ):
        assert f"`{non_false_pos}`" not in r3_missing_str, r3_missing_str

    # Synthetic valid spec citing module stems, Mathlib, sections, and Unicode decls must pass
    valid_doc = REPO_ROOT / "scratch" / "e2e_reconciliation" / "_tmp_doc_sym_valid.md"
    bad_doc = REPO_ROOT / "scratch" / "e2e_reconciliation" / "_tmp_doc_sym_bad.md"
    valid_doc.parent.mkdir(parents=True, exist_ok=True)
    try:
        valid_doc.write_text(
            "`GradedGraceContraction` `DirectLimit` `MonoidHom` `NormedAddCommGroup` "
            "`LinearIsometryEquiv` `IsManifold` `GeneralRing` `clifford_ι_injective` "
            "`InfoGeometry.Clifford.GradedGraceContraction.equivExterior_ι`\n",
            encoding="utf-8",
        )
        assert verify_doc_symbols([os.path.relpath(valid_doc, REPO_ROOT)])["passed"]

        fakes = [
            "NonExistentTheorem999",
            "CEFakeTheorem999",
            "Cl11FakeStruct",
            "OperatorAlgebra.FakeThm999",
            "InfoGeometry.Fake.clifford_ι_fake999",
            "fake_ι_theorem999",
            "InfoGeometry.FakeNamespace.Erlangen20Datum",
        ]
        bad_doc.write_text(" ".join(f"`{f}`" for f in fakes) + "\n", encoding="utf-8")
        bad_res = verify_doc_symbols([os.path.relpath(bad_doc, REPO_ROOT)])
        assert not bad_res["passed"]
        joined = "\n".join(bad_res["missing_symbols"])
        for fake in fakes:
            assert f"`{fake}`" in joined, f"Expected rejection of {fake}, got: {joined}"
    finally:
        valid_doc.unlink(missing_ok=True)
        bad_doc.unlink(missing_ok=True)


def test_f25_11_modules_and_functorial_bridges_registered():
    f25_targets = set(checks_by_id()["T2-F2.5-4"].spec["targets"])
    collected = set(_collect_m1_m2_m3_files())
    expected = {
        "lean/InfoGeometry/Erlangen/ErlangenProgramGroupHierarchyAndPrincipal.lean",
        "lean/InfoGeometry/Erlangen/ErlangenProgramTransferHesseAndBodies.lean",
        "lean/InfoGeometry/Erlangen/ErlangenProgramMobiusLieAndContact.lean",
        "lean/InfoGeometry/Erlangen/ErlangenProgramCurvatureBinaryAndMasterAtlas.lean",
        "lean/InfoGeometry/Projective/KleinErlangenProgramGroupsAndProjectiveTransfer.lean",
        "lean/InfoGeometry/Canonical/KleinErlangenSphereContactAndBinaryForms.lean",
        "lean/InfoGeometry/Projective/GrassmannPluckerMeetAndCircleSpace.lean",
        "lean/InfoGeometry/Canonical/GrassmannPfaffianSyzygyAndNormalForms.lean",
        "lean/InfoGeometry/Projective/PluckerKummerQuarticAndMasterAtlas.lean",
        "lean/InfoGeometry/Projective/PluckerRayAxisAndDyname.lean",
        "lean/InfoGeometry/Canonical/PluckerGrassmannKleinUnifiedSynthesis.lean",
        "lean/InfoGeometry/Erlangen/GrassmannPluckerKleinFunctorialBridges.lean",
    }
    assert expected <= f25_targets
    assert expected <= collected
    assert set(F2_5_BASELINE_ALL) <= collected
    assert "lean/InfoGeometry/OperatorAlgebra/ErlangenDoubleCylinderSymmetryInvariants.lean" in collected


@pytest.mark.parametrize("check", CHECKS, ids=[c.check_id for c in CHECKS])
def test_reconciliation_e2e_check(check: CheckSpec):
    mode = get_mode()
    if not is_active_for_mode(check, mode):
        pytest.skip(f"Gated on {check.gate}; run E2E_MODE=full for M4 acceptance")
    outcome = execute_check(check, mode)
    assert outcome.status == "PASS", f"[{check.check_id}] {outcome.summary}"
