from pathlib import Path


LEAN = Path("lean/InfoGeometry/Canonical/SouriauConformalKKTContext.lean").read_text()


def test_square_response_witness_surface_present():
    assert "structure ConformalSquareResponseWitness" in LEAN
    assert "theorem selfResponse_nonneg (X : EndH₂) (W : ConformalSquareResponseWitness C X)" in LEAN
    assert "def toConstructiveSquarePositiveContextOfWitness" in LEAN
    assert "def toPositiveContextOfWitness" in LEAN
    assert "theorem selfResponse_nonneg_of_squareWitness" in LEAN
    assert "namespace ConformalCartanOddPartitionWitness" in LEAN
    assert (
        "theorem selfResponse_nonneg_of_squareWitness\n"
        "    (W : ConformalCartanOddPartitionWitness"
    ) in LEAN
    assert (
        "def toPositiveContextOfWitness\n"
        "    (W : ConformalCartanOddPartitionWitness"
    ) in LEAN
    assert (
        "theorem fisherOnsagerProduction_nonneg_of_squareWitness\n"
        "    (W : ConformalCartanOddPartitionWitness"
    ) in LEAN
    assert "(hSquare : ConformalSquareResponseWitness C X)" in LEAN
    assert "(W.toPositiveContextOfWitness weylGauge tkkParameter hTKK hCone X Y" in LEAN
