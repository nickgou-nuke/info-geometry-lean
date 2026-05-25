from pathlib import Path


LEAN = Path("lean/InfoGeometry/Canonical/SouriauConformalKKTContext.lean").read_text()


def test_cartan_odd_tkk_cone_square_response_surface_present():
    assert (
        "noncomputable def toOperatorAdmissibilityWitnessOfTKKConeWitness\n"
        "    (W : ConformalCartanOddPartitionWitness"
    ) in LEAN
    assert (
        "theorem selfResponse_nonneg_of_squareWitness_of_TKKConeWitness\n"
        "    (W : ConformalCartanOddPartitionWitness"
    ) in LEAN
    assert (
        "theorem fisherOnsagerProduction_nonneg_of_squareWitness_of_TKKConeWitness\n"
        "    (W : ConformalCartanOddPartitionWitness"
    ) in LEAN
    assert "W.toOperatorAdmissibilityWitnessOfTKKConeWitness weylGauge hTKK hCone X Y" in LEAN
