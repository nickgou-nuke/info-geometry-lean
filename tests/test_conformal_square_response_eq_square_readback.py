from pathlib import Path


LEAN = Path("lean/InfoGeometry/Canonical/SouriauConformalKKTContext.lean").read_text()


def test_square_response_eq_square_readbacks_present() -> None:
    assert (
        "theorem fisherOnsagerProduction_eq_square_of_squareResponse\n"
        "    (W : ConformalPositivePartitionWitness C)"
    ) in LEAN
    assert (
        "theorem fisherOnsagerProduction_eq_square_of_squareResponse\n"
        "    (W : ConformalCartanOddPartitionWitness"
    ) in LEAN
    assert (
        "(W.toConstructiveSquarePositiveContext weylGauge tkkParameter hTKK hCone X Y\n"
        "      amplitude selfResponse_eq_square).fisherOnsagerProduction_eq_square"
    ) in LEAN
