from pathlib import Path


REPO = Path(__file__).resolve().parents[1]
OBSERVER_DEFECT = REPO / "lean" / "InfoGeometry" / "Canonical" / "ObserverDefect.lean"


def test_zero_zd_owner_iff_routes_exact_control_to_compressed_deviation_zero() -> None:
    text = OBSERVER_DEFECT.read_text(encoding="utf-8")

    assert "theorem compressedDeviation_eq_zero_of_deviationControlledByZD_of_ZD_eq_zero" in text
    assert "theorem compressedDeviation_eq_zero_iff_deviationControlledByZD_of_ZD_eq_zero" in text
    assert "observerDefectResidual_eq_zero_of_deviationControlledByZD_of_ZD_eq_zero" in text
    assert "observerDefectResidual_eq_projectorCompression_commutator_deviation" in text


def test_zero_zd_owner_iff_recovers_exact_control_from_compressed_deviation_zero() -> None:
    text = OBSERVER_DEFECT.read_text(encoding="utf-8")

    assert "observerDeviationControlledByZD_of_compressedDeviation_eq_zero" in text
    assert "compressedDeviation_eq_zero_of_deviationControlledByZD_of_ZD_eq_zero" in text
