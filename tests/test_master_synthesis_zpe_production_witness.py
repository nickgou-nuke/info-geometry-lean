from pathlib import Path


REPO = Path(__file__).resolve().parents[1]
SOURCE = REPO / "lean" / "InfoGeometry" / "Canonical" / "MasterSynthesis.lean"


def test_master_synthesis_exposes_zpe_production_witness_capstone_route() -> None:
    text = SOURCE.read_text(encoding="utf-8")

    assert (
        "private theorem bits_to_gravity_to_fluid_capstone_of_productionWitness_of_zpeGravityWitness"
        in text
    )
    block = text.split(
        "private theorem bits_to_gravity_to_fluid_capstone_of_productionWitness_of_zpeGravityWitness",
        1,
    )[1].split(
        "/--\nRegularization wrapper with internalized Drazin witness:", 1
    )[0]
    assert "(hZPEGravity : ZPEGravityWitness (E := E) S c R Kgeo x)" in block
    assert "(Wfluid : FluidHelicityProductionWitness (E := E) A B_mp B_dr)" in block
    assert "(hReg : RegularizationWitness" not in block
    assert "(hHelicity : MatchedHelicityWitness" not in block
    assert "bits_to_gravity_to_fluid_capstone_of_regularization_of_zpeGravityWitness" in block
    assert "Wfluid.regularization" in block
    assert "Wfluid.helicity" in block
