from pathlib import Path


REPO = Path(__file__).resolve().parents[1]
SOURCE = REPO / "lean" / "InfoGeometry" / "Canonical" / "BekensteinBound.lean"


def test_bekenstein_exposes_zero_normalized_cocycle_witness_route() -> None:
    text = SOURCE.read_text(encoding="utf-8")

    assert "structure ZeroNormalizedCocycleGeneratorWitness" in text
    assert "theorem topologicalBekensteinBound_of_zeroNormalizedCocycleGeneratorWitness" in text

    block = text.split(
        "theorem topologicalBekensteinBound_of_zeroNormalizedCocycleGeneratorWitness", 1
    )[1].split(
        "/--\nZero-normalized generator-lift route to the topological Bekenstein bound.", 1
    )[0]

    assert "(W : ZeroNormalizedCocycleGeneratorWitness" in block
    assert "(hBridge : ScalarCocycleBridge" not in block
    assert "(hLift :" not in block
    assert "(hZero :" not in block

    wrapper = text.split(
        "theorem topologicalBekensteinBound_of_connesCocycle_generatorLift_zero", 1
    )[1]
    assert "topologicalBekensteinBound_of_zeroNormalizedCocycleGeneratorWitness" in wrapper
    assert "{ hBridge := hBridge" in wrapper
    assert "hLift := hLift" in wrapper
    assert "hZero := cocycleEntropyPotential_zero_of_connesCocycle" in wrapper


def test_bekenstein_exposes_tomita_zero_normalized_witness_route() -> None:
    text = SOURCE.read_text(encoding="utf-8")

    assert (
        "theorem topologicalBekensteinBound_of_tomitaZeroNormalizedCocycleGeneratorWitness"
        in text
    )

    block = text.split(
        "theorem topologicalBekensteinBound_of_tomitaZeroNormalizedCocycleGeneratorWitness", 1
    )[1].split(
        "/--\nTomita-specialized zero-anchored cocycle-to-bound theorem.", 1
    )[0]
    assert "ZeroNormalizedCocycleGeneratorWitness" in block
    assert "(hBridge :" not in block
    assert "(hLift :" not in block
    assert "(hZero :" not in block

    wrapper = text.split(
        "theorem topologicalBekensteinBound_of_tomitaConnesCocycle_generatorLift_zero", 1
    )[1]
    assert "topologicalBekensteinBound_of_tomitaZeroNormalizedCocycleGeneratorWitness" in wrapper
    assert "{ hBridge := hBridge" in wrapper
    assert "hLift := hLift" in wrapper
    assert "hZero := cocycleEntropyPotential_zero_of_connesCocycle" in wrapper
