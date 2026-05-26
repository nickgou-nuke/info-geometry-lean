from pathlib import Path


REPO = Path(__file__).resolve().parents[1]
TRIALITY = REPO / "lean" / "InfoGeometry" / "LLM" / "TrialityMoE.lean"
OBSERVER = REPO / "lean" / "InfoGeometry" / "Canonical" / "ObserverDefect.lean"


def test_aligned_zd_bound_lives_on_owner_lane() -> None:
    triality_text = TRIALITY.read_text(encoding="utf-8")
    observer_text = OBSERVER.read_text(encoding="utf-8")

    owner_anchor = "theorem observerDeviationControlledByZD_of_aligned\n"

    assert owner_anchor in observer_text
    assert "ofControlObserver (E := E) CIK obs flow" in triality_text
    assert (
        "observerDeviationControl_of_aligned\n"
        "      (E := E) (CIK := CIK) (obs := obs) hAlign"
        in triality_text
    )
    assert owner_anchor not in triality_text


def test_aligned_observer_routes_through_owner_control_witness() -> None:
    triality_text = TRIALITY.read_text(encoding="utf-8")
    observer_text = OBSERVER.read_text(encoding="utf-8")

    assert "theorem observerDeviationControl_of_aligned" in observer_text
    assert "noncomputable def ofAlignedObserver" in triality_text
    assert "ofControlObserver (E := E) CIK obs flow" in triality_text
    assert "observerDeviationControl_of_aligned" in triality_text
