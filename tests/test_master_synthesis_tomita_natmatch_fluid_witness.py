from pathlib import Path


REPO = Path(__file__).resolve().parents[1]
SOURCE = REPO / "lean" / "InfoGeometry" / "Canonical" / "MasterSynthesis.lean"


def test_master_synthesis_exposes_tomita_natmatch_fluid_witness_capstone_route() -> None:
    text = SOURCE.read_text(encoding="utf-8")

    anchor = (
        "private theorem "
        "bits_to_gravity_to_fluid_capstone_tomita_cocycle_sourced_natMatch_fluidWitness"
    )
    assert anchor in text
    block = text.split(anchor, 1)[1].split(
        "/--\nTomita flow-unit cocycle-sourced capstone variant.", 1
    )[0]
    assert "(Wfluid : FluidHelicityProductionWitness (E := E) A B_mp B_dr)" in block
    assert "(ω : VelocityField E →L[ℝ] ℝ)" not in block
    assert "(Ω : AlgebraEnd E →L[ℝ] ℝ)" not in block
    assert "(hAnomalySkew :" not in block
    assert "(hHelicity : helicityInvariant A ω = twinWaveHelicity A Ω)" not in block
    assert "bits_to_gravity_to_fluid_capstone_tomita_cocycle_sourced_natMatch" in block
    assert "(ω := Wfluid.helicity.omega)" in block
    assert "(Ω := Wfluid.helicity.Omega)" in block
    assert "anomalySkew_of_regularizationWitness (E := E) A B_mp B_dr Wfluid.regularization" in block
    assert "(hHelicity := Wfluid.helicity.match_helicity)" in block
