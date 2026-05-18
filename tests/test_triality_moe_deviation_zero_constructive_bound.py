from pathlib import Path


REPO = Path(__file__).resolve().parents[1]
TRIALITY = REPO / "lean" / "InfoGeometry" / "LLM" / "TrialityMoE.lean"
OBSERVER = REPO / "lean" / "InfoGeometry" / "Canonical" / "ObserverDefect.lean"


def test_deviation_zero_observer_uses_theorem_backed_bound() -> None:
    triality_text = TRIALITY.read_text(encoding="utf-8")
    observer_text = OBSERVER.read_text(encoding="utf-8")

    owner_anchor = "theorem observerDeviationControlledByZD_of_deviation_eq_zero\n"

    assert "theorem observerDefectResidual_eq_zero_of_deviation_eq_zero" in observer_text
    assert owner_anchor in observer_text
    assert "ofZDControlledObserver (E := E) CIK obs flow" in triality_text
    assert (
        "observerDeviationControlledByZD_of_deviation_eq_zero\n"
        "      (E := E) (CIK := CIK) (obs := obs) hDev"
        in triality_text
    )
    assert owner_anchor not in triality_text
