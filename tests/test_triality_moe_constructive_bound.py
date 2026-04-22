from pathlib import Path


REPO = Path(__file__).resolve().parents[1]
TRIALITY = REPO / "lean" / "InfoGeometry" / "LLM" / "TrialityMoE.lean"
OBSERVER = REPO / "lean" / "InfoGeometry" / "Canonical" / "ObserverDefect.lean"


def test_aligned_observer_uses_theorem_backed_bound() -> None:
    triality_text = TRIALITY.read_text(encoding="utf-8")
    observer_text = OBSERVER.read_text(encoding="utf-8")

    assert "theorem observerDefectResidual_eq_zero_of_aligned" in observer_text
    assert "observerDefectResidual_norm_le_ZD_of_aligned (E := E) (CIK := CIK) (obs := obs)" in triality_text
