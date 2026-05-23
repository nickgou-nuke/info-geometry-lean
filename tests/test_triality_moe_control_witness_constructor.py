from pathlib import Path


REPO = Path(__file__).resolve().parents[1]
TRIALITY = REPO / "lean" / "InfoGeometry" / "LLM" / "TrialityMoE.lean"
OBSERVER = REPO / "lean" / "InfoGeometry" / "Canonical" / "ObserverDefect.lean"


def test_control_witness_constructor_routes_through_owner_packet() -> None:
    triality_text = TRIALITY.read_text(encoding="utf-8")
    observer_text = OBSERVER.read_text(encoding="utf-8")

    assert "structure ObserverDeviationControl" in observer_text
    assert "noncomputable def ofControlObserver" in triality_text
    assert "ObserverDeviationControlledByZD.of_control c" in triality_text
    assert "theorem ofControlObserver_routerResidual_eq_zero_of_ZD_eq_zero" in triality_text


def test_control_witness_constructor_has_sourced_generator_and_cut_readbacks() -> None:
    triality_text = TRIALITY.read_text(encoding="utf-8")

    assert "theorem ofControlObserver_sourcedGenerator_eq_flow_of_ZD_eq_zero" in triality_text
    assert "theorem ofControlObserver_sourcedGenerator_respects_cut_of_ZD_eq_zero" in triality_text
    assert "theorem ofControlObserver_observerDefectResidual_eq_zero_of_ZD_eq_zero" in triality_text
    assert "theorem ofControlObserver_observerOrientationStrain_eq_zero_of_ZD_eq_zero" in triality_text
    assert "(c : ObserverDeviationControl CIK obs)" in triality_text
    assert "(hZD :" in triality_text
    assert "observerOrientationStrain CIK obs = 0 := by" in triality_text
    assert "simpa [ofControlObserver] using" in triality_text
    assert "ofZDControlledObserver_sourcedGenerator_eq_flow_of_ZD_eq_zero" in triality_text
    assert "observerDefectResidual_eq_zero_of_deviationControlledByZD_of_ZD_eq_zero" in triality_text
    assert "observerOrientationStrain_eq_zero_iff (CIK := CIK) (obs := obs)" in triality_text
    assert "rw [ofControlObserver_sourcedGenerator_eq_flow_of_ZD_eq_zero" in triality_text
