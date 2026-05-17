from pathlib import Path


REPO = Path(__file__).resolve().parents[1]
SOURCE = REPO / "lean" / "InfoGeometry" / "Canonical" / "MasterSynthesis.lean"


def test_master_synthesis_exposes_diii_thermal_bott_witness_capstone_route() -> None:
    text = SOURCE.read_text(encoding="utf-8")

    anchor = (
        "private theorem "
        "bits_to_gravity_to_fluid_capstone_with_nonzero_scale_and_diii_"
        "transportCommutator_of_quasilatticeAnalyticalIndex_of_"
        "mismatch_forces_projector_noncommute_of_ownerWitnesses_and_"
        "productionWitness_and_thermalBottWitness"
    )
    assert anchor in text

    block = text.split(anchor, 1)[1].split(
        "/--\nOwner-path capstone composition:", 1
    )[0]

    assert "(hThermalBott : ThermalBottWitness (E := E))" in block
    assert "(Wfluid : FluidHelicityProductionWitness (E := E) A B_mp B_dr)" in block
    assert "(W : DIIITransportCommutatorWitness (E := E) hThermalBott.V Xdef hXdef tdef)" in block
    assert "(Mod : ModularRadonNikodymData E)" not in block
    assert "(V : BogoliubovVielbein.BogoliubovVielbeinBundle" not in block
    assert "(IST : InfoSpectralTriple H₂)" not in block
    assert "(hCompat : InformationalLichnerowiczBottCompatibility" not in block
    assert "bits_to_gravity_to_fluid_capstone_with_nonzero_scale_and_diii_transportCommutator" in block
    assert "(Mod := hThermalBott.Mod)" in block
    assert "(V := hThermalBott.V)" in block
    assert "(IST := hThermalBott.IST)" in block
    assert "(hCompat := hThermalBott.hCompat)" in block
