from pathlib import Path


REPO = Path(__file__).resolve().parents[1]
CASIMIR = REPO / "lean" / "InfoGeometry" / "Canonical" / "CasimirWeylDrazinContext.lean"
OBSERVER = REPO / "lean" / "InfoGeometry" / "Canonical" / "ObserverDefect.lean"


def test_sourced_generator_background_has_nonempty_control_route() -> None:
    casimir_text = CASIMIR.read_text(encoding="utf-8")
    observer_text = OBSERVER.read_text(encoding="utf-8")

    assert "theorem sourcedGenerator_eq_background_of_nonempty_control_of_ZD_eq_zero" in casimir_text
    assert "observerOrientationStrain_eq_zero_of_nonempty_control_of_ZD_eq_zero" in observer_text
    assert "sourcedGenerator_eq_background_of_strain_eq_zero_of_ZD_eq_zero" in casimir_text
