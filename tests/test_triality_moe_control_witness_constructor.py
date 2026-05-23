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


def test_control_witness_constructor_uses_direct_owner_strain_readback() -> None:
    triality_text = TRIALITY.read_text(encoding="utf-8")

    assert "theorem ofControlObserver_observerOrientationStrain_eq_zero_of_ZD_eq_zero" in triality_text
    assert "observerOrientationStrain_eq_zero_of_deviationControlledByZD_of_ZD_eq_zero" in triality_text
    assert "ObserverDeviationControlledByZD.of_control c" in triality_text
