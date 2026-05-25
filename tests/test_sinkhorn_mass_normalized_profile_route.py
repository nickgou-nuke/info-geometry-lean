from pathlib import Path


REPO = Path(__file__).resolve().parents[1]
SINKHORN = REPO / "lean" / "InfoGeometry" / "LLM" / "SinkhornDefectFlow.lean"


def test_mass_normalized_count_profiles_route_directly_to_sinkhorn_profile_lifts() -> None:
    text = SINKHORN.read_text(encoding="utf-8")

    assert "noncomputable def SinkhornRNBarrierProfileLift.ofMassNormalizedRowCounts" in text
    assert "noncomputable def SinkhornRNBarrierProfileLift.ofMassNormalizedColCounts" in text
    assert "RowRNBarrierCountProfileLift.ofMassNormalized" in text
    assert "ColRNBarrierCountProfileLift.ofMassNormalized" in text
    assert "PhaseRNBarrierProfileLift.ofRowCounts" in text
    assert "PhaseRNBarrierProfileLift.ofColCounts" in text


def test_mass_normalized_count_profiles_route_directly_to_operator_readout_bound() -> None:
    text = SINKHORN.read_text(encoding="utf-8")

    assert "theorem operatorInformationNormReadout_le_of_massNormalizedRowCounts" in text
    assert "theorem operatorInformationNormReadout_le_of_massNormalizedColCounts" in text
    assert "operatorInformationNormReadout_le_of_sinkhornRNBarrierProfile" in text
    assert "SinkhornRNBarrierProfileLift.ofMassNormalizedRowCounts" in text
    assert "SinkhornRNBarrierProfileLift.ofMassNormalizedColCounts" in text
