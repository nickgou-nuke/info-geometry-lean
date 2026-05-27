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
        "/--\nZero-normalized generator-lift route to increment-level RN-barrier control.", 1
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
    assert (
        "theorem topologicalBekensteinBound_of_tomitaFlowUnitZeroNormalizedCocycleGeneratorWitness"
        in text
    )
    assert (
        "theorem topologicalBekensteinBound_of_tomitaFlowUnitConnesCocycle_generatorLift_zero"
        in text
    )

    block = text.split(
        "theorem topologicalBekensteinBound_of_tomitaZeroNormalizedCocycleGeneratorWitness", 1
    )[1].split(
        "/--\nTomita flow-unit zero-normalized witness endpoint on the canonical welded cocycle lane.", 1
    )[0]
    assert "ZeroNormalizedCocycleGeneratorWitness" in block
    assert "(hBridge :" not in block
    assert "(hLift :" not in block
    assert "(hZero :" not in block

    flow_unit_block = text.split(
        "theorem topologicalBekensteinBound_of_tomitaFlowUnitZeroNormalizedCocycleGeneratorWitness", 1
    )[1].split(
        "/--\nTomita-specialized zero-anchored cocycle-to-bound theorem.", 1
    )[0]
    assert "(W : ZeroNormalizedCocycleGeneratorWitness" in flow_unit_block
    assert "flowUnitCocycle" in flow_unit_block
    assert "(hBridge :" not in flow_unit_block
    assert "(hLift :" not in flow_unit_block
    assert "(hZero :" not in flow_unit_block

    wrapper = text.split(
        "theorem topologicalBekensteinBound_of_tomitaFlowUnitConnesCocycle_generatorLift_zero", 1
    )[1]
    assert (
        "topologicalBekensteinBound_of_tomitaFlowUnitZeroNormalizedCocycleGeneratorWitness"
        in wrapper
    )
    assert "{ hBridge := InfoGeometry.Volume.ConnesCocycle.unitScalarBridge" in wrapper
    assert "hLift := hLift" in wrapper
    assert "hZero := cocycleEntropyPotential_zero_of_connesCocycle" in wrapper
