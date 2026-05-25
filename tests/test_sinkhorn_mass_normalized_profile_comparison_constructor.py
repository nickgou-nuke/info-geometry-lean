from pathlib import Path


REPO = Path(__file__).resolve().parents[1]
SINKHORN = REPO / "lean" / "InfoGeometry" / "LLM" / "SinkhornDefectFlow.lean"


def test_mass_normalized_count_routes_have_direct_profile_comparison_constructors() -> None:
    text = SINKHORN.read_text(encoding="utf-8")

    assert "noncomputable def WeylThermodynamicProfileComparison.ofMassNormalizedRowCounts" in text
    assert "noncomputable def WeylThermodynamicProfileComparison.ofMassNormalizedColCounts" in text
    assert "WeylThermodynamicProfileComparison.ofSinkhornRNBarrier" in text
    assert "SinkhornRNBarrierProfileLift.ofMassNormalizedRowCounts" in text
    assert "SinkhornRNBarrierProfileLift.ofMassNormalizedColCounts" in text


def test_mass_normalized_operator_readout_theorems_use_direct_profile_comparison_constructors() -> None:
    text = SINKHORN.read_text(encoding="utf-8")

    assert "WeylThermodynamicProfileComparison.ofMassNormalizedRowCounts" in text
    assert "WeylThermodynamicProfileComparison.ofMassNormalizedColCounts" in text
    assert "operatorInformationNormReadout_le_of_weylThermodynamicProfileComparison" in text
