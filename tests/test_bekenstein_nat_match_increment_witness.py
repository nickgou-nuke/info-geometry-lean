from pathlib import Path


REPO = Path(__file__).resolve().parents[1]
SOURCE = REPO / "lean" / "InfoGeometry" / "Canonical" / "BekensteinBound.lean"


def test_bekenstein_exposes_cocycle_nat_match_increment_witness_route() -> None:
    text = SOURCE.read_text(encoding="utf-8")

    assert "structure CocycleNatMatchWitness" in text
    assert "theorem cocycleIncrement_abs_le_trajectoryRNBarrier_of_cocycleNatMatchWitness" in text

    block = text.split(
        "theorem cocycleIncrement_abs_le_trajectoryRNBarrier_of_cocycleNatMatchWitness", 1
    )[1].split(
        "/--\nProof-carrying zero-normalized cocycle generator packet.", 1
    )[0]

    assert "(W : CocycleNatMatchWitness" in block
    assert "(hBridge : ScalarCocycleBridge" not in block
    assert "    (hMatch :\n" not in block
    assert "cocycleIncrement_abs_le_trajectoryRNBarrier_of_natMatch" in block
    assert "(hBridge := W.hBridge)" in block
    assert "(hMatch := W.hMatch)" in block
