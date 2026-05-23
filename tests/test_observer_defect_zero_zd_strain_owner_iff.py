from pathlib import Path


REPO = Path(__file__).resolve().parents[1]
OBSERVER_DEFECT = REPO / "lean" / "InfoGeometry" / "Canonical" / "ObserverDefect.lean"


def test_zero_zd_owner_iff_routes_strain_to_exact_control() -> None:
    text = OBSERVER_DEFECT.read_text(encoding="utf-8")

    assert "theorem observerOrientationStrain_eq_zero_iff_deviationControlledByZD_of_ZD_eq_zero" in text
    assert "observerDeviationControlledByZD_of_strain_eq_zero" in text
    assert "observerDefectResidual_eq_zero_of_deviationControlledByZD_of_ZD_eq_zero" in text
    assert "observerOrientationStrain_eq_zero_iff (CIK := CIK) (obs := obs)" in text


def test_zero_zd_owner_iff_has_constructive_control_witness_route() -> None:
    text = OBSERVER_DEFECT.read_text(encoding="utf-8")

    assert "theorem observerDeviationControl_of_strain_eq_zero" in text
    assert "theorem observerOrientationStrain_eq_zero_of_control_of_ZD_eq_zero" in text
    assert "ObserverDeviationControlledByZD.of_control c" in text
