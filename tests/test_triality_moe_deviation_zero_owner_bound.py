from pathlib import Path


REPO = Path(__file__).resolve().parents[1]
TRIALITY = REPO / "lean" / "InfoGeometry" / "LLM" / "TrialityMoE.lean"
OBSERVER = REPO / "lean" / "InfoGeometry" / "Canonical" / "ObserverDefect.lean"


def test_deviation_zero_zd_bound_lives_on_owner_lane() -> None:
    triality_text = TRIALITY.read_text(encoding="utf-8")
    observer_text = OBSERVER.read_text(encoding="utf-8")

    owner_anchor = "theorem observerDefectResidual_norm_le_ZD_of_deviation_eq_zero\n"

    assert owner_anchor in observer_text
    assert (
        "observerDefectResidual_norm_le_ZD_of_deviation_eq_zero (E := E) (CIK := CIK) (obs := obs) hDev"
        in triality_text
    )
    assert owner_anchor not in triality_text
