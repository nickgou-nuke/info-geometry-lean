from pathlib import Path


REPO = Path(__file__).resolve().parents[1]
SOURCE = REPO / "lean" / "InfoGeometry" / "Canonical" / "MasterSynthesis.lean"


def test_master_synthesis_exposes_mismatch_constructive_witness_route() -> None:
    text = SOURCE.read_text(encoding="utf-8")

    anchor = (
        "private theorem "
        "bits_to_gravity_to_fluid_capstone_with_nonzero_scale_of_"
        "quasilatticeIndexMismatchWitness_of_constructiveWitness"
    )
    assert anchor in text

    block = text.split(anchor, 1)[1].split(
        "/--\nDefect-sourced capstone + DIII commutator wrapper:", 1
    )[0]

    assert (
        "(W : ConstructiveMasterCapstoneWitness (E := E) S c R Kgeo x A B_mp B_dr)"
        in block
    )
    assert "(Wmismatch : QuasilatticeIndexMismatchWitness" in block
    assert "(hZPEGravity : ZPEGravityWitness" not in block
    assert "(Wfluid : FluidHelicityProductionWitness" not in block
    assert "(hThermalBott : ThermalBottWitness" not in block
    assert "    (hMismatchNoncommute :\n" not in block
    assert "    (hIndexNonzero : quasilatticeAnalyticalIndex" not in block
    assert (
        "bits_to_gravity_to_fluid_capstone_with_nonzero_scale_of_"
        "quasilatticeAnalyticalIndex_of_mismatch_forces_projector_noncommute_of_"
        "ownerWitnesses_and_productionWitness"
    ) in block
    assert "(hZPEGravity := W.zpeGravity)" in block
    assert "(Wfluid := W.fluidProduction)" in block
    assert "(Mod := W.thermalBott.Mod)" in block
    assert "(V := W.thermalBott.V)" in block
    assert "(IST := W.thermalBott.IST)" in block
    assert "(hCompat := W.thermalBott.hCompat)" in block
    assert "(hMismatchNoncommute := Wmismatch.hMismatchNoncommute)" in block
    assert "(hIndexNonzero := Wmismatch.hIndexNonzero)" in block
