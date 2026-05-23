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


def test_router_sourced_generator_iff_and_strain_route() -> None:
    triality_text = TRIALITY.read_text(encoding="utf-8")

    assert "theorem sourcedGenerator_eq_flow_iff_routerResidual_eq_zero" in triality_text
    assert "theorem ofStrainZeroObserver_sourcedGenerator_eq_flow" in triality_text
    assert "(sourcedGenerator_eq_flow_iff_routerResidual_eq_zero" in triality_text
    assert "ofStrainZeroObserver_routerResidual" in triality_text


def test_control_constructor_sourced_generator_of_strain_zero() -> None:
    triality_text = TRIALITY.read_text(encoding="utf-8")

    assert "theorem ofControlObserver_sourcedGenerator_eq_flow_of_strain_eq_zero" in triality_text
    assert "observerDefectResidual_eq_zero_of_strain_eq_zero" in triality_text
    assert "(sourcedGenerator_eq_flow_iff_routerResidual_eq_zero" in triality_text
    assert "ofControlObserver (E := E) CIK obs flow c" in triality_text
