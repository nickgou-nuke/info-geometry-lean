from pathlib import Path

from tools.quality.closure_debt_crawler import (
    apply_repo_wide_laundering_audit,
    audit_file,
    build_payload,
)


def test_proof_hole_only_flags_sorry_admit_not_sorryAx(tmp_path: Path) -> None:
    lean = tmp_path / "Demo.lean"
    lean.write_text(
        """
import Mathlib

def meta_marker : String := "sorryAx"

theorem ok : True := by
  trivial
""",
        encoding="utf-8",
    )

    report = audit_file(lean)
    categories = {f.category for f in report.findings}

    assert "proof-hole" not in categories
    # `sorryAx` appearing in inert metadata/string context must not hard-fail as a proof hole.


def test_proof_hole_ignores_lean_docstrings_and_trace_names(tmp_path: Path) -> None:
    lean = tmp_path / "Metadata.lean"
    lean.write_text(
        """
/-! This documentation discusses sorry and admit as audit vocabulary. -/
initialize registerTraceClass `Example.admit

/-- The implementation is complete; the word `sorry` is documentation only. -/
def implemented : Nat := 0
""",
        encoding="utf-8",
    )

    report = audit_file(lean)
    assert [f for f in report.findings if f.category == "proof-hole"] == []


def test_current_meta_and_lint_owners_have_no_hard_proof_holes() -> None:
    root = Path(__file__).resolve().parents[1]
    paths = (
        root / "lean/DAG/ExactMorphism.lean",
        root / "lean/InfoGeometry/Lint/Pauli.lean",
        root / "lean/InfoGeometry/Meta/Trust.lean",
    )

    for path in paths:
        report = audit_file(path)
        hard_holes = [
            f for f in report.findings
            if f.category == "proof-hole" and f.severity == "hard"
        ]
        assert hard_holes == [], f"stale proof-hole finding for {path}: {hard_holes}"


def test_payload_contains_provenance_and_hard_verdict_fields(tmp_path: Path) -> None:
    lean = tmp_path / "Hard.lean"
    lean.write_text(
        """
import Mathlib

theorem bad : True := by
  sorry
""",
        encoding="utf-8",
    )

    report = audit_file(lean)
    payload = build_payload(tmp_path, [report])

    assert payload["schema"] == "info_geometry.closure_debt_crawler.v2"
    assert payload["authority_tier"] == "heuristic-proxy"
    assert payload["summary"]["provenance"]["hard_failures"] >= 1

    first = payload["files"][0]["findings"][0]
    assert "graph_grounded_signal" in first
    assert "heuristic_signal" in first
    assert "hard_verdict_allowed" in first


def test_detects_structure_law_lockers_classical_witness_and_local_hypothesis(tmp_path: Path) -> None:
    lean = tmp_path / "Debt.lean"
    lean.write_text(
        """
import Mathlib

structure LawLocker where
  carrier : Type
  impossible_law : ∀ x : Nat, x = x

noncomputable def smuggled (h : Nonempty Nat) : Nat :=
  Classical.choice h

theorem local_bridge (n : Nat) : n = n := by
  have h : n = n := by
    rfl
  exact h
""",
        encoding="utf-8",
    )

    report = audit_file(lean)
    categories = {f.category for f in report.findings}

    assert "law-field-locker" in categories
    assert "classical-witness-smuggling" in categories
    assert "local-hypothesis-injection" in categories


def test_repo_wide_audit_detects_uninstantiated_law_locker_and_single_use_bridge(
    tmp_path: Path,
) -> None:
    lean = tmp_path / "BridgeDebt.lean"
    lean.write_text(
        """
import Mathlib

structure PhantomPacket where
  law : ∀ n : Nat, n = n

lemma bridge_to_goal (n : Nat) : n = n := by
  rfl

theorem downstream (n : Nat) : n = n := by
  exact bridge_to_goal n
""",
        encoding="utf-8",
    )

    report = audit_file(lean)
    [repo_report] = apply_repo_wide_laundering_audit([lean], [report])
    categories = {f.category for f in repo_report.findings}

    assert "uninstantiated-law-locker" in categories
    assert "single-use-evidence-bridge" in categories


def test_detects_simp_law_variable_notation_partial_and_cast_bypasses(tmp_path: Path) -> None:
    lean = tmp_path / "SilentCheats.lean"
    lean.write_text(
        """
import Mathlib

variable (fake_law : ∀ n : Nat, n = n)

local notation "TRUTHY" => True

@[simp] theorem bridge_simp_law (n : Nat) : n = n := by
  rfl

partial def loopish (n : Nat) : Nat :=
  loopish n

theorem casty (p q : Prop) (h : p = q) : p → q := by
  exact Eq.mp h
""",
        encoding="utf-8",
    )

    report = audit_file(lean)
    categories = {f.category for f in report.findings}

    assert "section-law-variable" in categories
    assert "notation-or-macro-warp" in categories
    assert "simp-law-injection" in categories
    assert "partial-bypass" in categories
    assert "definitional-equality-bypass" in categories
