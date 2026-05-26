from pathlib import Path


REPO = Path(__file__).resolve().parents[1]
OBSERVER_DEFECT = REPO / "lean" / "InfoGeometry" / "Canonical" / "ObserverDefect.lean"


def test_zero_strain_constructs_observer_defect_zd_control() -> None:
    text = OBSERVER_DEFECT.read_text(encoding="utf-8")

    assert "theorem observerDefectResidual_eq_zero_of_strain_eq_zero" in text
    assert "theorem observerDefectResidual_norm_le_ZD_of_strain_eq_zero" in text
    assert "theorem observerDeviationControlledByZD_of_strain_eq_zero" in text
    assert "observerOrientationStrain_eq_zero_iff" in text
    assert "observerDefectResidual_eq_zero_of_strain_eq_zero (CIK := CIK) (obs := obs) hStrain" in text


def test_compressed_deviation_zero_forces_zero_strain() -> None:
    text = OBSERVER_DEFECT.read_text(encoding="utf-8")

    assert "theorem observerOrientationStrain_eq_zero_of_compressedDeviation_eq_zero" in text
    assert "observerDefectResidual_eq_zero_of_compressedDeviation_eq_zero" in text
    assert "observerOrientationStrain_eq_zero_iff" in text


def test_deviation_zero_forces_zero_strain() -> None:
    text = OBSERVER_DEFECT.read_text(encoding="utf-8")

    assert "theorem observerOrientationStrain_eq_zero_of_deviation_eq_zero" in text
    assert "observerDefectResidual_eq_zero_of_deviation_eq_zero" in text
    assert "observerOrientationStrain_eq_zero_iff" in text
    assert "observerDefectResidual_eq_zero_of_deviation_eq_zero" in text


def test_deviation_zero_constructs_control_witness_packet() -> None:
    text = OBSERVER_DEFECT.read_text(encoding="utf-8")

    assert "theorem observerDeviationControl_of_deviation_eq_zero" in text
    assert "theorem observerDeviationControlledByZD_of_deviation_eq_zero" in text
    assert "{ bound := observerDeviationControlledByZD_of_deviation_eq_zero" in text
