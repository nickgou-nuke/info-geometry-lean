from pathlib import Path


REPO = Path(__file__).resolve().parents[1]
SOURCE = REPO / "lean" / "InfoGeometry" / "Canonical" / "MasterSynthesis.lean"


def test_master_synthesis_exposes_constructive_witness_squeezing_route() -> None:
    text = SOURCE.read_text(encoding="utf-8")

    anchor = (
        "private theorem "
        "squeezingLogShear_bound_of_bits_to_gravity_to_fluid_capstone_of_constructiveWitness"
    )
    assert anchor in text
    block = text.split(anchor, 1)[1].split(
        "/--\nCanonical-Drazin witness squeezing corollary", 1
    )[0]
    assert (
        "(W : ConstructiveMasterCapstoneWitness (E := E) S c R Kgeo x A B_mp B_dr)"
        in block
    )
    assert "(hZPEGravity : ZPEGravityWitness" not in block
    assert "(Wfluid : FluidHelicityProductionWitness" not in block
    assert "(hThermalBott : ThermalBottWitness" not in block
    assert "bits_to_gravity_to_fluid_capstone_of_constructiveWitness" in block
    assert "(Mod := W.thermalBott.Mod)" in block
    assert "(IST := W.thermalBott.IST)" in block
