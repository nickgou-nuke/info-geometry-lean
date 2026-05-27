from pathlib import Path


REPO = Path(__file__).resolve().parents[1]
SOURCE = REPO / "lean" / "InfoGeometry" / "Canonical" / "SouriauConformalKKTContext.lean"


def test_conformal_positive_partition_witness_has_direct_closure_constructor():
    text = SOURCE.read_text()

    assert "namespace ConformalPositivePartitionWitness" in text
    assert "noncomputable def toOperatorAdmissibilityWitness" in text
    assert "noncomputable def toClosureContext" in text
    assert "partitionWitness := W" in text
    assert "without re-supplying a separate `hOperatorAdmissible` packet" in text



def test_conformal_positive_partition_has_tkk_cone_square_witness_routes():
    text = SOURCE.read_text()

    assert "theorem selfResponse_nonneg_of_squareWitness_of_TKKConeWitness" in text
    assert "theorem selfResponse_nonneg_of_squareResponse_of_TKKConeWitness" in text
    assert "theorem fisherOnsagerProduction_nonneg_of_squareWitness_of_TKKConeWitness" in text
    assert "theorem fisherOnsagerProduction_nonneg_of_squareResponse_of_TKKConeWitness" in text
    assert "theorem fisherOnsagerProduction_eq_square_of_squareWitness_of_TKKConeWitness" in text
    assert "theorem fisherOnsagerProduction_eq_square_of_squareResponse_of_TKKConeWitness" in text
    assert "W.toOperatorAdmissibilityWitnessOfTKKConeWitness weylGauge hTKK hCone X Y" in text
    assert "(ConformalOperatorAdmissibilityWitness.toPositiveContext\n      (W := W.toOperatorAdmissibilityWitnessOfTKKConeWitness weylGauge hTKK hCone X Y)" in text
