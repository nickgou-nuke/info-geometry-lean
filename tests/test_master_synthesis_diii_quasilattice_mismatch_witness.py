from pathlib import Path


REPO = Path(__file__).resolve().parents[1]
SOURCE = REPO / "lean" / "InfoGeometry" / "Canonical" / "MasterSynthesis.lean"


def test_master_synthesis_exposes_diii_quasilattice_mismatch_witness_route() -> None:
    text = SOURCE.read_text(encoding="utf-8")

    structure_anchor = "private structure QuasilatticeIndexMismatchWitness"
    assert structure_anchor in text

    theorem_anchor = (
        "private theorem "
        "bits_to_gravity_to_fluid_capstone_with_nonzero_scale_and_diii_"
        "transportCommutator_of_quasilatticeIndexMismatchWitness_of_"
        "zpeGravityWitness_and_productionWitness_and_thermalBottWitness"
    )
    assert theorem_anchor in text

    block = text.split(theorem_anchor, 1)[1].split(
        "/--\nOwner-path capstone composition:", 1
    )[0]

    assert "(Wmismatch : QuasilatticeIndexMismatchWitness" in block
    assert "    (hMismatchNoncommute :\n" not in block
    assert "    (hIndexNonzero : quasilatticeAnalyticalIndex" not in block
    assert (
        "bits_to_gravity_to_fluid_capstone_with_nonzero_scale_and_diii_"
        "transportCommutator_of_quasilatticeAnalyticalIndex_of_"
        "mismatch_forces_projector_noncommute_of_zpeGravityWitness_and_"
        "productionWitness_and_thermalBottWitness"
    ) in block
    assert "(hMismatchNoncommute := Wmismatch.hMismatchNoncommute)" in block
    assert "(hIndexNonzero := Wmismatch.hIndexNonzero)" in block
