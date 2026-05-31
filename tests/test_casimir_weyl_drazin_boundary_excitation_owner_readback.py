from pathlib import Path


REPO = Path(__file__).resolve().parents[1]
CASIMIR = REPO / "lean" / "InfoGeometry" / "Canonical" / "CasimirWeylDrazinContext.lean"


def test_boundary_excitation_owner_readback_theorems_exist() -> None:
    text = CASIMIR.read_text(encoding="utf-8")

    assert "theorem sourcedGenerator_boundary_excitation_eq_background_iff_observerDefectResidual_eq_zero" in text
    assert "theorem sourcedGenerator_boundary_excitation_eq_background_iff_compressedDeviation_eq_zero" in text
    assert "theorem sourcedGenerator_boundary_excitation_eq_background_of_compressedDeviation_eq_zero" in text
    assert "theorem sourcedGenerator_boundary_excitation_eq_background_of_deviationControlledByZD_of_ZD_eq_zero" in text
    assert "theorem sourcedGenerator_boundary_excitation_eq_background_iff_deviationControlledByZD_of_ZD_eq_zero" in text
    assert "theorem sourcedGenerator_eq_background_iff_observerDefectResidual_norm_le_ZD_of_ZD_eq_zero" in text
    assert "theorem sourcedGenerator_eq_background_of_observerDefectResidual_norm_le_ZD_of_ZD_eq_zero" in text


def test_boundary_excitation_owner_readback_routes_through_existing_owner_theorems() -> None:
    text = CASIMIR.read_text(encoding="utf-8")

    assert "sourcedGenerator_boundary_excitation (E := E) CIK C" in text
    assert "observerDefectResidual_eq_zero_of_deviationControlledByZD_of_ZD_eq_zero" in text
    assert "observerOrientationStrain_eq_zero_iff_deviationControlledByZD_of_ZD_eq_zero" in text
    assert "observerDefectResidual_eq_projectorCompression_commutator_deviation" in text
    assert "observerDeviationControlledByZD_iff_observerDefectResidual_norm_le_ZD" in text
    assert "(sourcedGenerator_eq_background_iff_observerDefectResidual_norm_le_ZD_of_ZD_eq_zero" in text
