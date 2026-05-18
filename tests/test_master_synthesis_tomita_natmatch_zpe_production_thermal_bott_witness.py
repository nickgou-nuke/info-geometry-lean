from pathlib import Path


REPO = Path(__file__).resolve().parents[1]
SOURCE = REPO / "lean" / "InfoGeometry" / "Canonical" / "MasterSynthesis.lean"


def test_master_synthesis_exposes_tomita_natmatch_zpe_production_thermal_bott_witness_capstone_route() -> None:
    text = SOURCE.read_text(encoding="utf-8")

    anchor = (
        "private theorem "
        "bits_to_gravity_to_fluid_capstone_tomita_cocycle_sourced_natMatch_"
        "of_zpeGravityWitness_and_productionWitness_and_thermalBottWitness"
    )
    assert anchor in text
    block = text.split(anchor, 1)[1].split(
        "/--\nTomita flow-unit cocycle-sourced capstone variant.", 1
    )[0]
    assert "(hZPEGravity : ZPEGravityWitness (E := E) S c R Kgeo x)" in block
    assert "(Wfluid : FluidHelicityProductionWitness (E := E) A B_mp B_dr)" in block
    assert "(hThermalBott : ThermalBottWitness (E := E))" in block
    assert "(hRankPos : 0 < Module.finrank ℝ E)" not in block
    assert "(hEin : IsEinsteinKaehlerAtWith c R Kgeo x)" not in block
    assert "(Mod : ModularRadonNikodymData E)" not in block
    assert "(V : BogoliubovVielbein.BogoliubovVielbeinBundle (E := E))" not in block
    assert "(IST : InfoSpectralTriple H₂)" not in block
    assert "(hCompat : InformationalLichnerowiczBottCompatibility" not in block
    assert "bits_to_gravity_to_fluid_capstone_tomita_cocycle_sourced_natMatch_fluidWitness" in block
    assert "(hRankPos := hZPEGravity.hRankPos)" in block
    assert "(hEin := hZPEGravity.hEin)" in block
    assert "(Mod := hThermalBott.Mod)" in block
    assert "(V := hThermalBott.V)" in block
    assert "(IST := hThermalBott.IST)" in block
    assert "(hCompat := hThermalBott.hCompat)" in block
