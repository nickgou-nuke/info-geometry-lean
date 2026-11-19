from __future__ import annotations

from pathlib import Path

from tools.quality import detect_hollow_theorems as dht


def test_detect_hollow_theorems_flags_blocking_holes_and_vacuous_proofs(tmp_path: Path, capsys) -> None:
    target = tmp_path / "Bad.lean"
    target.write_text(
        """
theorem withSorry : 1 = 1 := by
  sorry

lemma withAdmit : 1 = 1 := by
  admit

theorem trivialTrue : True := trivial

theorem trueIntro : True := by exact True.intro

theorem justAssumption (h : 2 = 2) : 2 = 2 := by assumption
""",
        encoding="utf-8",
    )

    rc = dht.main(["--strict", str(target)])
    out = capsys.readouterr().out

    assert rc == 1
    assert "withSorry [hollow]" in out
    assert "withAdmit [hollow]" in out
    assert "trivialTrue [hollow]" in out
    assert "trueIntro [hollow]" in out
    assert "justAssumption [hollow]" in out


def test_detect_hollow_theorems_passes_valid_code_and_advisory_only_abs_nonneg(tmp_path: Path, capsys) -> None:
    target = tmp_path / "Good.lean"
    target.write_text(
        """
-- sorry in comment must be ignored
def plainDef : True := trivial

@[simp] theorem simpRfl (x : Nat) : x = x := rfl

theorem helperNonneg (x : Int) : 0 ≤ |x| := by exact abs_nonneg x

theorem realProof (n : Nat) : n + 0 = n := by
  induction n with
  | zero => rfl
  | succ k ih => simp [ih]
""",
        encoding="utf-8",
    )

    rc = dht.main(["--strict", str(target)])
    out = capsys.readouterr().out

    assert rc == 0
    assert "plainDef" not in out
    assert "simpRfl" not in out
    assert "withSorry" not in out
    assert "helperNonneg [hollow-advisory]" in out


def test_detect_hollow_theorems_missing_target_returns_2_in_strict_mode(tmp_path: Path, capsys) -> None:
    rc = dht.main(["--strict", str(tmp_path / "DoesNotExist.lean")])
    err = capsys.readouterr().err

    assert rc == 2
    assert "target not found" in err
