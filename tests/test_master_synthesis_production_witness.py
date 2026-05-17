from pathlib import Path


REPO = Path(__file__).resolve().parents[1]
SOURCE = REPO / "lean" / "InfoGeometry" / "Canonical" / "MasterSynthesis.lean"


def test_master_synthesis_exposes_production_witness_capstone_route() -> None:
    text = SOURCE.read_text(encoding="utf-8")

    assert "private theorem bits_to_gravity_to_fluid_capstone_of_productionWitness" in text
    block = text.split(
        "private theorem bits_to_gravity_to_fluid_capstone_of_productionWitness", 1
    )[1].split(
        "/--\nRegularization capstone with the ZPE/gravity owner packet.", 1
    )[0]
    assert "(Wfluid : FluidHelicityProductionWitness (E := E) A B_mp B_dr)" in block
    assert "(hReg : RegularizationWitness" not in block
    assert "(hHelicity : MatchedHelicityWitness" not in block
    assert "bits_to_gravity_to_fluid_capstone_of_regularization" in block
    assert "Wfluid.regularization" in block
    assert "Wfluid.helicity" in block
