from pathlib import Path


REPO = Path(__file__).resolve().parents[1]
SOURCE = REPO / "lean" / "InfoGeometry" / "Canonical" / "BekensteinBound.lean"


def test_bekenstein_exposes_minimal_casini_witness_route() -> None:
    text = SOURCE.read_text(encoding="utf-8")

    assert "structure MinimalCasiniIncrementWitness" in text
    assert "theorem cocycleIncrement_abs_le_trajectoryRNBarrier_of_minimalCasiniIncrementWitness" in text
    assert "theorem topologicalBekensteinBound_of_minimalCasiniIncrementWitness" in text

    increment_block = text.split(
        "theorem cocycleIncrement_abs_le_trajectoryRNBarrier_of_minimalCasiniIncrementWitness", 1
    )[1].split(
        "theorem topologicalBekensteinBound_of_minimalCasiniIncrementWitness", 1
    )[0]

    assert "(W : MinimalCasiniIncrementWitness" in increment_block
    assert "(hBridge : ScalarCocycleBridge" not in increment_block
    assert "(relEnt : RelativeEntropyProfile)" not in increment_block
    assert "(hCasini : MinimalCasiniIncrementBridge" not in increment_block
    assert "cocycleIncrement_abs_le_trajectoryRNBarrier_of_minimalCasiniIncrement" in increment_block
    assert "(hBridge := W.hBridge)" in increment_block
    assert "(relEnt := W.relEnt)" in increment_block
    assert "(hCasini := W.hCasini)" in increment_block

    block = text.split(
        "theorem topologicalBekensteinBound_of_minimalCasiniIncrementWitness", 1
    )[1].split(
        "theorem topologicalBekensteinBound_of_minimalCasiniIncrement", 1
    )[0]

    assert "(W : MinimalCasiniIncrementWitness" in block
    assert "(hBridge : ScalarCocycleBridge" not in block
    assert "(relEnt : RelativeEntropyProfile)" not in block
    assert "(hCasini : MinimalCasiniIncrementBridge" not in block

    wrapper = text.split(
        "theorem topologicalBekensteinBound_of_minimalCasiniIncrement", 1
    )[1].split(
        "/--\nCasini-route cocycle-to-bound compatibility wrapper:", 1
    )[0]
    assert "topologicalBekensteinBound_of_minimalCasiniIncrementWitness" in wrapper
    assert "{ hBridge := hBridge" in wrapper
    assert "relEnt := relEnt" in wrapper
    assert "hCasini := hCasini" in wrapper
