from pathlib import Path


REPO = Path(__file__).resolve().parents[1]
SOURCE = REPO / "lean" / "InfoGeometry" / "Canonical" / "MasterSynthesis.lean"


def test_master_synthesis_exposes_diii_zpe_production_thermal_bott_witness_capstone_route() -> None:
    text = SOURCE.read_text(encoding="utf-8")

    anchor = (
        "private theorem "
        "bits_to_gravity_to_fluid_capstone_with_nonzero_scale_and_diii_"
        "transportCommutator_of_quasilatticeAnalyticalIndex_of_"
        "mismatch_forces_projector_noncommute_of_zpeGravityWitness_and_"
        "productionWitness_and_thermalBottWitness"
    )
    assert anchor in text

    block = text.split(anchor, 1)[1].split(
        "/--\nOwner-path capstone composition:", 1
    )[0]

    assert "(hZPEGravity : ZPEGravityWitness (E := E) Sstate c R Kgeo x)" in block
    assert "(Wfluid : FluidHelicityProductionWitness (E := E) A B_mp B_dr)" in block
    assert "(hThermalBott : ThermalBottWitness (E := E))" in block
    assert "(hRankPos : 0 < Module.finrank ℝ E)" not in block
    assert "(hEin : IsEinsteinKaehlerAtWith c R Kgeo x)" not in block
    assert (
        "bits_to_gravity_to_fluid_capstone_with_nonzero_scale_and_diii_"
        "transportCommutator_of_quasilatticeAnalyticalIndex_of_"
        "mismatch_forces_projector_noncommute_of_ownerWitnesses_and_"
        "productionWitness_and_thermalBottWitness"
    ) in block
    assert "(hZPEGravity := hZPEGravity)" not in block
    assert "(hRankPos := hZPEGravity.hRankPos)" in block
    assert "(hEin := hZPEGravity.hEin)" in block
    assert "(Wfluid := Wfluid)" in block
    assert "(hThermalBott := hThermalBott)" in block
